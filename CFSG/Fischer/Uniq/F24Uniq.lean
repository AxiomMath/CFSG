module

public import CFSG.Fischer.Uniq.Fi23Facts
public import CFSG.Fischer.Uniq.F23Uniq
public import CFSG.Fischer.Uniq.LHTransport
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1011
public import Certificates.Certificate1012
public import Certificates.Certificate1000
public import CFSG.Fischer.Polar.Lines
public import CFSG.Sporadic.Fi23.Graph

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

section ModelGeneric

variable {Y Z : Type} [Group Y] [Group Z] {F : Set Y} {C : Set Z} (hPF : PolarFacts)
  (hF : F22 Y F) (hconnF : (commGraph F).Connected) (hC : Pair Z C)
  (hconn : (commGraph C).Connected)
  (hlocC : ∀ f ∈ C, Nonempty (LocalPoints (pairModel hF.1) C f))
include hPF hF hconnF hC hconn hlocC

theorem Pair.isLocallyHyperoval_muSet_of_model (hF1 : LinesByPerp) {p q : Z} (hp : p ∈ C)
    (hq : q ∈ C) (hpq : q * p ≠ p * q) :
    (muSet C p q).Nonempty ∧ IsLocallyHyperoval (LocalClass C p) (muSet C p q) := by
  have hne := Pair.muSet_nonempty hC hconn hp hq hpq
  refine ⟨hne, ?_⟩
  obtain ⟨L⟩ := hlocC p hp
  have hqf : q ∈ farSet C p := ⟨hq, hpq, hne⟩
  have h1 := Pair.isLocallyHyperoval_muImg hPF hF1 hF hconnF hC hlocC hp hqf L
  have hinv : ∀ x ∈ F, x * x = 1 := fun x hx => Pair.mul_self hF.1 hx
  have h2 := h1.transport L.χ.symm (comm_symm_of_comm _ L.comm)
    (tau_symm_of_tau _ fun x y => ⟨LocalPoints.mul_mul_mem_localClass hC x y,
      congrArg Subtype.val (L.tau x y _)⟩) hinv
  convert h2 using 1
  ext s
  constructor
  · intro hs
    refine ⟨L.χ ⟨s, hs.1⟩, ⟨_, ⟨⟨s, hs.1⟩, hs.2, rfl⟩, rfl⟩, ?_⟩
    rw [Equiv.symm_apply_apply]
  · rintro ⟨y, ⟨_, ⟨t, ht, rfl⟩, hty⟩, rfl⟩
    have : y = L.χ t := Subtype.ext hty.symm
    rw [this, Equiv.symm_apply_apply]
    exact ⟨t.2, ht⟩

theorem muSet_fib_of_model {p q q' : Z} (hp : p ∈ C) (hq : q ∈ C) (hq' : q' ∈ C)
    (hpq : q * p ≠ p * q) (hpq' : q' * p ≠ p * q') (h : muSet C p q = muSet C p q') :
    q' = q ∨ q' = p * q * p := by
  obtain ⟨L⟩ := hlocC p hp
  have hqf : q ∈ farSet C p := ⟨hq, hpq, Pair.muSet_nonempty hC hconn hp hq hpq⟩
  have hqf' : q' ∈ farSet C p := ⟨hq', hpq', Pair.muSet_nonempty hC hconn hp hq' hpq'⟩
  refine L.muImg_fib_of_model hPF hF hconnF hC hlocC hp hqf hqf' ?_
  ext r
  rw [← Equiv.apply_symm_apply L.χ r, L.χ_mem_muImg_iff, L.χ_mem_muImg_iff, h]

end ModelGeneric

section Model23

open CFSG.Sporadic.Fi23

variable (hPF : PolarFacts)
include hPF

theorem isLocallyHyperoval_muSet_D23
    (hHF : HyperovalFacts) (p q : J) (hp : p ∈ D23)
    (hq : q ∈ D23) (hpq : q * p ≠ p * q) : (muSet D23 p q).Nonempty ∧
      IsLocallyHyperoval (LocalClass D23 p) (muSet D23 p q) :=
  Pair.isLocallyHyperoval_muSet_of_model hPF Sporadic.Fi22.f22_J Sporadic.Fi22.connected_D pair_J
    (connected_D23 hPF) (localPoints_D23 hPF) hHF.linesByPerp hp hq hpq

theorem muSet_fib_D23
    {p q q' : J} (hp : p ∈ D23) (hq : q ∈ D23) (hq' : q' ∈ D23)
    (hpq : q * p ≠ p * q) (hpq' : q' * p ≠ p * q') (h : muSet D23 p q = muSet D23 p q') :
    q' = q ∨ q' = p * q * p :=
  muSet_fib_of_model hPF Sporadic.Fi22.f22_J Sporadic.Fi22.connected_D pair_J (connected_D23 hPF)
    (localPoints_D23 hPF) hp hq hq' hpq hpq' h

end Model23

section Fi23Model

open CFSG.Sporadic.Fi23

variable (hPF : PolarFacts) (hHF : HyperovalFacts) {tr cs : Set (Set D23)}
  {r : tr} (hTF : Fi23Facts tr cs r) (hE : Pair X E)
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel pair_J) E f))
include hPF hHF hTF hE hloc

omit hHF hTF in
theorem LocalPoints.muImg_fib_of_fi23
    {d : X} (hd : d ∈ E)
    (L : LocalPoints (pairModel pair_J) E d) {c c' : X} (hc : c ∈ farSet E d)
    (hc' : c' ∈ farSet E d) (h : L.muImg c = L.muImg c') :
    c' = c ∨ c' = d * c * d := by
  have hmu := L.muSet_eq_of_muImg_eq h
  obtain ⟨f, hf⟩ := hc.2.2
  have hf' : f ∈ muSet E d c' := hmu ▸ hf
  have hdf : d ∈ LocalClass E f := ⟨hd, hf.1.2.1.symm, hf.1.2.2.symm⟩
  have hcf : c ∈ LocalClass E f := ⟨hc.1, hf.2.2.1.symm, hf.2.2.2.symm⟩
  have hc'f : c' ∈ LocalClass E f := ⟨hc'.1, hf'.2.2.1.symm, hf'.2.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f hf.1.1
  set p := Lf.χ ⟨d, hdf⟩
  set q := Lf.χ ⟨c, hcf⟩
  set q' := Lf.χ ⟨c', hc'f⟩
  have hpq : (q : J) * p ≠ p * q := fun e => hc.2.1 ((Lf.comm ⟨c, hcf⟩ ⟨d, hdf⟩).2 e)
  have hpq' : (q' : J) * p ≠ p * q' := fun e => hc'.2.1 ((Lf.comm ⟨c', hc'f⟩ ⟨d, hdf⟩).2 e)
  have key : ∀ c₀ (hc₀ : c₀ ∈ LocalClass E f), ∀ g : LocalClass E f,
      ((Lf.χ g : D23) : J) ∈ muSet D23 (p : J) (Lf.χ ⟨c₀, hc₀⟩ : J) ↔
        (g : X) ∈ muSet E d c₀ := by
    intro c₀ hc₀ g
    rw [muSet, Set.mem_inter_iff, ← Lf.mem_localClass_iff pair_J ⟨d, hdf⟩ g,
      ← Lf.mem_localClass_iff pair_J ⟨c₀, hc₀⟩ g]
    rfl
  have hmuF : muSet D23 (p : J) (q : J) = muSet D23 (p : J) (q' : J) := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := Lf.χ.surjective ⟨y, hy.1.1⟩
      have hy' : ((Lf.χ g : D23) : J) ∈ muSet D23 (p : J) (q : J) := by rw [hg]; exact hy
      rw [key c hcf g, hmu, ← key c' hc'f g, hg] at hy'
      exact hy'
    · intro hy
      obtain ⟨g, hg⟩ := Lf.χ.surjective ⟨y, hy.1.1⟩
      have hy' : ((Lf.χ g : D23) : J) ∈ muSet D23 (p : J) (q' : J) := by rw [hg]; exact hy
      rw [key c' hc'f g, ← hmu, ← key c hcf g, hg] at hy'
      exact hy'
  rcases muSet_fib_D23 hPF p.2 q.2 q'.2 hpq hpq' hmuF with e | e
  · left
    exact congrArg Subtype.val (Lf.χ.injective (Subtype.ext e))
  · right
    have hdcd : d * c * d ∈ LocalClass E f :=
      LocalPoints.mul_mul_mem_localClass hE (⟨d, hdf⟩ : LocalClass E f) ⟨c, hcf⟩
    have h1 := congrArg Subtype.val (Lf.tau ⟨d, hdf⟩ ⟨c, hcf⟩ hdcd)
    rw [pairModel_tv] at h1
    rw [← e] at h1
    exact (congrArg Subtype.val (Lf.χ.injective (Subtype.ext h1))).symm

theorem LocalPoints.muImg_mem_tr
    {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel pair_J) E d) : L.muImg c ∈ tr := by
  have hlh := Pair.isLocally351_muImg pair_J hE
    (fun p q hp hq hpq => isLocallyHyperoval_muSet_D23 hPF hHF p q hp hq hpq) hloc hd hc L
  rcases hTF.classify _ hlh ((L.muImg_nonempty_iff c).2 hc.2.2) with hcs | htr
  · exfalso
    obtain ⟨v, w, hv, hw, hvw, heq⟩ := hTF.cs_not_inj _ hcs
    set f := L.χ.symm v
    set f' := L.χ.symm w
    have hfv : L.χ f = v := Equiv.apply_symm_apply _ _
    have hfw : L.χ f' = w := Equiv.apply_symm_apply _ _
    have hfc : (f : X) ∉ muSet E d c := by rw [← L.χ_mem_muImg_iff, hfv]; exact hv
    have hf'c : (f' : X) ∉ muSet E d c := by rw [← L.χ_mem_muImg_iff, hfw]; exact hw
    have h1 : L.muImg (d * c * f * c * d) = L.muImg (d * c * f' * c * d) := by
      rw [L.muImg_nu hE hd hc.1 hc.2.1 f hfc, L.muImg_nu hE hd hc.1 hc.2.1 f' hf'c, hfv, hfw,
        heq]
    rcases LocalPoints.muImg_fib_of_fi23 hPF hE hloc hd L
      (nu_mem_farSet hE hd hc f hfc) (nu_mem_farSet hE hd hc f' hf'c) h1 with e | e
    · apply hvw
      rw [← hfv, ← hfw]
      congr 1
      exact Subtype.ext (nu_injective d c e).symm
    ·
      set g := d * c * f * c * d
      have hgE : g ∈ E := (nu_mem_farSet hE hd hc f hfc).1
      have hgd : g * d ≠ d * g := (nu_mem_farSet hE hd hc f hfc).2.1
      have hcg : c * g = g * c := ((Pair.nu_mem_localClass hE hd hc.1 hc.2.1 f.2).2.2).symm
      have hcg' : c * (d * g * d) = d * g * d * c := by
        rw [← e]; exact ((Pair.nu_mem_localClass hE hd hc.1 hc.2.1 f'.2).2.2).symm
      apply hc.2.1
      have hline : g * (d * g * d) * g = d := by
        rw [← Pair.mul_mul_eq hE hgE hd hgd, Pair.mul_mul_mul_mul hE hgE]
      rw [← hline]
      have h1' : Commute c g := hcg
      have h2' : Commute c (d * g * d) := hcg'
      exact ((h1'.mul_right h2').mul_right h1').eq
  · exact htr

theorem Pair.ncard_muSet_of_fi23
    {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d) :
    (muSet E d c).ncard = 3240 := by
  obtain ⟨L⟩ := hloc d hd
  rw [← L.ncard_muImg, hTF.ncard_of_mem_tr _ (L.muImg_mem_tr hPF hHF hTF hE hloc hd hc)]

theorem Pair.ncard_farSet_of_fi23
    {d : X} (hd : d ∈ E) : (farSet E d).ncard = 275264 := by
  have hk : ∀ {f}, f ∈ E → (LocalClass E f).ncard = 31671 := fun hf => by
    obtain ⟨L⟩ := hloc _ hf
    rw [← Nat.card_coe_set_eq, Nat.card_congr L.χ]
    exact card_class_d
  have hstar23 : ∀ p ∈ D23, (LocalClass D23 p).ncard = 3510 := fun p hp => by
    obtain ⟨Lp⟩ := localPoints_D23 hPF p hp
    rw [← Nat.card_coe_set_eq, Nat.card_congr Lp.χ, Nat.card_coe_set_eq, ncard_D]
  have hl : ∀ f ∈ LocalClass E d, (LocalClass E d ∩ LocalClass E f).ncard = 3510 := by
    intro f hf
    obtain ⟨L⟩ := hloc d hd
    rw [← Nat.card_coe_set_eq, Nat.card_congr (L.restrictStar pair_J ⟨f, hf⟩),
      Nat.card_coe_set_eq]
    exact hstar23 _ (L.χ ⟨f, hf⟩).2
  have h := Pair.ncard_farSet hE hd (hk hd) (fun f hf => hk hf.1) hl
    (fun c hc => Pair.ncard_muSet_of_fi23 hPF hHF hTF hE hloc hd hc)
  omega

theorem LocalPoints.family_eq_tr
    {d : X} (hd : d ∈ E) (L : LocalPoints (pairModel pair_J) E d) :
    L.muImg '' farSet E d = tr := by
  have := Pair.finite hE
  set 𝒮 := L.muImg '' farSet E d with h𝒮
  have hsub : 𝒮 ⊆ tr := by
    rintro _ ⟨c, hc, rfl⟩
    exact L.muImg_mem_tr hPF hHF hTF hE hloc hd hc
  have hcard := Pair.ncard_farSet_of_fi23 hPF hHF hTF hE hloc hd
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  have h2 := ncard_mul_eq_ncard_mul (fun c O => L.muImg c = O) (s := farSet E d) (t := 𝒮)
    (m := 1) (n := 2) (fun c hc => ?_) (fun O hO => ?_)
  · rw [hcard] at h2
    rw [hTF.ncard_tr]
    omega
  · have : {O | O ∈ 𝒮 ∧ L.muImg c = O} = {L.muImg c} := by
      ext O
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨⟨c, hc, rfl⟩, rfl⟩
    rw [this, Set.ncard_singleton]
  · obtain ⟨c₁, hc₁, rfl⟩ := hO
    have : {c | c ∈ farSet E d ∧ L.muImg c = L.muImg c₁} = {c₁, d * c₁ * d} := by
      ext c
      constructor
      · rintro ⟨hc, h⟩
        exact L.muImg_fib_of_fi23 hPF hE hloc hd hc₁ hc h.symm
      · rintro (rfl | rfl)
        · exact ⟨hc₁, rfl⟩
        · exact ⟨conj_mem_farSet hE hd hc₁, L.muImg_conj hE hd hc₁.1 hc₁.2.1⟩
    rw [this, Set.ncard_pair (Pair.mul_mul_ne_right hE hd (fun e => hc₁.2.1 e.symm)).symm]

theorem coverHyp_tr
    {d : X} (hd : d ∈ E) (L : LocalPoints (pairModel pair_J) E d) :
    CoverHyp L tr where
  mem c hc := L.family_eq_tr hPF hHF hTF hE hloc hd ▸ ⟨c, hc, rfl⟩
  surj O hO := by
    rw [← L.family_eq_tr hPF hHF hTF hE hloc hd] at hO
    obtain ⟨c, hc, rfl⟩ := hO
    exact ⟨c, hc, rfl⟩
  inj O hO := hTF.injOn_tv_image O hO
  ne O hO f hf := hTF.tv_image_ne O hO f hf
  fib _ hc _ hc' h := L.muImg_fib_of_fi23 hPF hE hloc hd hc hc' h

theorem Pair.not_commute_of_muSet_subset_fi23
    {a b y : X} (ha : a ∈ E) (hb : b ∈ E)
    (hab : a * b ≠ b * a) (hne : (muSet E a b).Nonempty) (hyE : y ∈ E)
    (hsub : muSet E a b ⊆ LocalClass E y) (hya : y ≠ a) : y * a ≠ a * y := by
  intro hya'
  obtain ⟨La⟩ := hloc a ha
  have hyl : y ∈ LocalClass E a := ⟨hyE, hya, hya'⟩
  have hbf : b ∈ farSet E a := ⟨hb, fun h => hab h.symm, hne⟩
  have hi := La.muImg_mem_tr hPF hHF hTF hE hloc ha hbf
  by_cases hp : La.χ ⟨y, hyl⟩ ∈ La.muImg b
  · have : y ∈ muSet E a b := (La.χ_mem_muImg_iff ⟨y, hyl⟩).1 hp
    exact (hsub this).2.1 rfl
  · obtain ⟨z, hz, hnc⟩ := hTF.exists_not_commute _ hi _ hp
    have hsmu : (La.χ.symm z : X) ∈ muSet E a b := ⟨(La.χ.symm z).2, La.mem_muImg.1 hz⟩
    have hcomm := (hsub hsmu).2.2
    apply hnc
    have := (La.comm ⟨y, hyl⟩ (La.χ.symm z)).1 hcomm.symm
    rwa [Equiv.apply_symm_apply] at this

theorem Pair.ySet_subset_of_fi23
    {e x : X} (he : e ∈ E) (hx : x ∈ E) (hex : e * x ≠ x * e)
    (hmu : (muSet E e x).Nonempty) : ySet E e x ⊆ {e, x, e * x * e} := by
  have := Pair.finite hE
  rintro y ⟨hyE, hS⟩
  by_cases hye : y = e
  · exact Or.inl hye
  by_cases hyx : y = x
  · exact Or.inr (Or.inl hyx)
  right; right
  have h1 := Pair.not_commute_of_muSet_subset_fi23 hPF hHF hTF hE hloc he hx hex hmu hyE hS
    hye
  have hxfar : x ∈ farSet E e := ⟨hx, fun h => hex h.symm, hmu⟩
  have hsub : muSet E e x ⊆ muSet E e y := fun s hs => ⟨hs.1, hS hs⟩
  have hyfar : y ∈ farSet E e := ⟨hyE, h1, hmu.mono hsub⟩
  have heq : muSet E e x = muSet E e y := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Pair.ncard_muSet_of_fi23 hPF hHF hTF hE hloc he hyfar,
      Pair.ncard_muSet_of_fi23 hPF hHF hTF hE hloc he hxfar]) (Set.toFinite _)
  obtain ⟨Le⟩ := hloc e he
  have himg : Le.muImg x = Le.muImg y := by
    ext p
    rw [← Equiv.apply_symm_apply Le.χ p, Le.χ_mem_muImg_iff, Le.χ_mem_muImg_iff, heq]
  rcases Le.muImg_fib_of_fi23 hPF hE hloc he hxfar hyfar himg with h | h
  · exact absurd h hyx
  · exact h

end Fi23Model

theorem F24.nonempty_compGraphIso'
    (hPF : PolarFacts) (hHF : HyperovalFacts)
    {tr cs : Set (Set Sporadic.Fi23.D23)} {r : tr} (hTF : Fi23Facts tr cs r)
    (hE : Pair X E) (hF : Pair Y F)
    (hlocE : ∀ f ∈ E, Nonempty (LocalPoints (pairModel Sporadic.Fi23.pair_J) E f))
    (hlocF : ∀ f ∈ F, Nonempty (LocalPoints (pairModel Sporadic.Fi23.pair_J) F f)) {d : X}
    {d' : Y} (hd : d ∈ E) (hd' : d' ∈ F) : Nonempty (compGraph E d ≃g compGraph F d') := by
  obtain ⟨L⟩ := hlocE d hd
  obtain ⟨L'⟩ := hlocF d' hd'
  have h := coverHyp_tr hPF hHF hTF hE hlocE hd L
  have h' := coverHyp_tr hPF hHF hTF hF hlocF hd' L'
  obtain ⟨β, hβπ, hβadj⟩ := TwoCover.exists_iso r hTF.xi24_D2 hTF.xi24_MU hTF.xi24_ED
    (coverOf hE hd L h) (coverOf hF hd' L' h')
  let βA : farSet E d ≃ farSet F d' := β
  have hπ : ∀ c, L'.muImg (βA c) = L.muImg c := fun c => congrArg Subtype.val (hβπ c)
  exact ⟨compGraphIso hd hd' L L' βA hπ hβadj⟩

theorem F24.exists_mulEquiv
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    {tr cs : Set (Set Sporadic.Fi23.D23)} {r : tr} (hTF : Fi23Facts tr cs r)
    (hE : F24 X E) (hF : F24 Y F) (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hSE : IsSimpleGroup (commutator X)) (hSF : IsSimpleGroup (commutator Y)) :
    ∃ φ : X ≃* Y, φ '' E = F := by
  have hlocE : ∀ f ∈ E, Nonempty (LocalPoints (pairModel Sporadic.Fi23.pair_J) E f) :=
    fun _ hf => Sporadic.Fi23.F24.nonempty_localPoints_fi23 hPF hHF hFF hE hf
  have hlocF : ∀ f ∈ F, Nonempty (LocalPoints (pairModel Sporadic.Fi23.pair_J) F f) :=
    fun _ hf => Sporadic.Fi23.F24.nonempty_localPoints_fi23 hPF hHF hFF hF hf
  have hmem : ∀ {Z : Type} [Group Z] {C : Set Z}, Pair Z C →
      (∀ f ∈ C, Nonempty (LocalPoints (pairModel Sporadic.Fi23.pair_J) C f)) →
      ∃ d ∈ C, ∃ f, f ∈ LocalClass C d := by
    intro Z _ C hP hloc
    obtain ⟨e, he⟩ := hP.2.1
    have hd : e ∈ C := by rw [he]; exact IsConj.refl e
    obtain ⟨L⟩ := hloc e hd
    exact ⟨e, hd, L.χ.symm ⟨Sporadic.Fi23.d, Sporadic.Fi23.d_mem_D23⟩, (L.χ.symm _).2⟩
  obtain ⟨d, hd, f, hf⟩ := hmem hE.1 hlocE
  obtain ⟨d', hd', f', hf'⟩ := hmem hF.1 hlocF
  have hconnE := Pair.connected_of_simple hE.1 hSE ⟨d, f, hd, hf.1, hf.2.1.symm, hf.2.2.symm⟩
  have hconnF := Pair.connected_of_simple hF.1 hSF ⟨d', f', hd', hf'.1, hf'.2.1.symm, hf'.2.2.symm⟩
  have huE : compSet E d = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hE.1 hconnE hd hc hcd
  have huF : compSet F d' = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hF.1 hconnF hd' hc hcd
  obtain ⟨ι⟩ := F24.nonempty_compGraphIso' hPF hHF hTF hE.1 hF.1 hlocE hlocF hd hd'
  let β : commGraph E ≃g commGraph F :=
    (compGraphIsoTop huE).symm.trans (ι.trans (compGraphIsoTop huF))
  refine Pair.mulEquiv_of_graphIso hE.1 hF.1 hZE hZF β fun e x he hx hex => ?_
  exact Pair.ySet_subset_of_fi23 hPF hHF hTF hF.1 hlocF he hx hex
    (Pair.muSet_nonempty hF.1 hconnF he hx fun h => hex h.symm)

end CFSG.Fischer
