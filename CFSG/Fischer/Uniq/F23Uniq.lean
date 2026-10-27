module

public import CFSG.Fischer.Uniq.Fi22Facts
public import CFSG.Fischer.Uniq.F23
public import CFSG.Fischer.Uniq.CompTau
public import Certificates.Certificate1001
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1004
public import Certificates.Certificate1005
public import Certificates.Certificate1006
public import Certificates.Certificate1009
public import Certificates.Certificate1010
public import Certificates.Certificate1000
public import CFSG.Fischer.Polar.Lines

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer CFSG.Sporadic.Fi22

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem ncard_D : (D : Set J).ncard = 3510 := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr ptD, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_localClass_D
    {p : J} (hp : p ∈ D) : (LocalClass D p).ncard = 693 :=
  ncard_localClass_of_polar (fun _ hf => F22.nonempty_localPoints f22_J hf) hp

section Fi22Model

variable (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts) (hE : Pair X E)
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel pair_D) E f))
include hPF hHF hFF hE hloc

theorem LocalPoints.exists_muImg_mem_lhOrbit
    {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d)
    (L : LocalPoints (pairModel pair_D) E d) : ∃ i, L.muImg c ∈ lhOrbit i :=
  hFF.exists_mem_lhOrbit _ (Pair.isLocallyHyperoval_muImg hPF hHF.linesByPerp f22_J connected_D hE
    hloc hd hc L) ((L.muImg_nonempty_iff c).2 hc.2.2)

theorem Pair.ncard_muSet_of_fi22
    {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d) :
    (muSet E d c).ncard = 351 := by
  obtain ⟨L⟩ := hloc d hd
  obtain ⟨i, hi⟩ := L.exists_muImg_mem_lhOrbit hPF hHF hFF hE hloc hd hc
  rw [← L.ncard_muImg, hFF.ncard_of_mem_lhOrbit i _ hi]

theorem Pair.ncard_farSet_of_fi22
    {d : X} (hd : d ∈ E) : (farSet E d).ncard = 28160 := by
  have hk : ∀ {f}, f ∈ E → (LocalClass E f).ncard = 3510 := fun hf => by
    rw [ncard_localClass_of_model f22_J hloc hf, ncard_D]
  have hl : ∀ f ∈ LocalClass E d, (LocalClass E d ∩ LocalClass E f).ncard = 693 := by
    intro f hf
    obtain ⟨p, hp, h⟩ := ncard_localClass_inter_of_model f22_J hloc hd hf
    rw [h, ncard_localClass_D hp]
  have h := Pair.ncard_farSet hE hd (hk hd) (fun f hf => hk hf.1) hl
    (fun c hc => Pair.ncard_muSet_of_fi22 hPF hHF hFF hE hloc hd hc)
  omega

theorem LocalPoints.exists_family_eq_lhOrbit
    {d : X} (hd : d ∈ E)
    (L : LocalPoints (pairModel pair_D) E d) : ∃ i, L.muImg '' farSet E d = lhOrbit i := by
  have := Pair.finite hE
  set 𝒮 := L.muImg '' farSet E d with h𝒮
  have hinv : ∀ O ∈ 𝒮, ∀ p, (pairModel pair_D).tv p '' O ∈ 𝒮 := by
    rintro O ⟨c, hc, rfl⟩ p
    refine ⟨_, Pair.star_conj_mem_farSet hE (L.χ.symm p) hc, ?_⟩
    rw [L.muImg_star_conj hE, Equiv.apply_symm_apply]
  have hcard := Pair.ncard_farSet_of_fi22 hPF hHF hFF hE hloc hd
  obtain ⟨c₀, hc₀⟩ := Set.nonempty_of_ncard_ne_zero (s := farSet E d) (by rw [hcard]; norm_num)
  obtain ⟨i, hi⟩ := L.exists_muImg_mem_lhOrbit hPF hHF hFF hE hloc hd hc₀
  refine ⟨i, (Set.eq_of_subset_of_ncard_le
    (hFF.lhOrbit_subset_of_invariant 𝒮 hinv i _ ⟨c₀, hc₀, rfl⟩ hi) ?_ (Set.toFinite _)).symm⟩
  have h2 := ncard_mul_eq_ncard_mul (fun c O => L.muImg c = O) (s := farSet E d) (t := 𝒮)
    (m := 1) (n := 2) (fun c hc => ?_) (fun O hO => ?_)
  · rw [hcard] at h2
    rw [hFF.ncard_lhOrbit i]
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
        exact L.muImg_fib_of_model hPF f22_J connected_D hE hloc hd hc₁ hc h.symm
      · rintro (rfl | rfl)
        · exact ⟨hc₁, rfl⟩
        · exact ⟨conj_mem_farSet hE hd hc₁, L.muImg_conj hE hd hc₁.1 hc₁.2.1⟩
    rw [this, Set.ncard_pair (Pair.mul_mul_ne_right hE hd (fun e => hc₁.2.1 e.symm)).symm]

omit hPF hHF hE hloc in
theorem LocalPoints.family_relabel_lhU {d : X} (L : LocalPoints (pairModel pair_D) E d) :
    (L.relabel lhU hFF.lhU_commute hFF.lhU_tv).muImg '' farSet E d =
      (fun O => ⇑lhU '' O) '' (L.muImg '' farSet E d) := by
  rw [Set.image_image]
  exact Set.image_congr fun c _ => L.muImg_relabel _ _ _ c

theorem exists_localPoints_lhOrbit_zero
    {d : X} (hd : d ∈ E) :
    ∃ L : LocalPoints (pairModel pair_D) E d, L.muImg '' farSet E d = lhOrbit 0 := by
  obtain ⟨L⟩ := hloc d hd
  obtain ⟨i, hi⟩ := L.exists_family_eq_lhOrbit hPF hHF hFF hE hloc hd
  set L₁ := L.relabel lhU hFF.lhU_commute hFF.lhU_tv
  have h₁ : L₁.muImg '' farSet E d = lhOrbit (i + 1) := by
    rw [L.family_relabel_lhU hFF, hi, hFF.image_lhU_lhOrbit]
  fin_cases i
  · exact ⟨L, hi⟩
  · exact ⟨L₁, h₁⟩

omit hHF in
theorem coverHyp_lhOrbit_zero
    {d : X} (hd : d ∈ E) (L : LocalPoints (pairModel pair_D) E d)
    (hL : L.muImg '' farSet E d = lhOrbit 0) : CoverHyp L (lhOrbit 0) where
  mem c hc := hL ▸ ⟨c, hc, rfl⟩
  surj O hO := by
    rw [← hL] at hO
    obtain ⟨c, hc, rfl⟩ := hO
    exact ⟨c, hc, rfl⟩
  inj O hO := hFF.injOn_tv_image O hO
  ne O hO f hf := hFF.tv_image_ne O hO f hf
  fib _ hc _ hc' h := L.muImg_fib_of_model hPF f22_J connected_D hE hloc hd hc hc' h

theorem Pair.not_commute_of_muSet_subset_fi22
    {a b y : X} (ha : a ∈ E) (hb : b ∈ E)
    (hab : a * b ≠ b * a) (hne : (muSet E a b).Nonempty) (hyE : y ∈ E)
    (hsub : muSet E a b ⊆ LocalClass E y) (hya : y ≠ a) : y * a ≠ a * y := by
  intro hya'
  obtain ⟨La⟩ := hloc a ha
  have hyl : y ∈ LocalClass E a := ⟨hyE, hya, hya'⟩
  have hbf : b ∈ farSet E a := ⟨hb, fun h => hab h.symm, hne⟩
  obtain ⟨i, hi⟩ := La.exists_muImg_mem_lhOrbit hPF hHF hFF hE hloc ha hbf
  by_cases hp : La.χ ⟨y, hyl⟩ ∈ La.muImg b
  · have : y ∈ muSet E a b := (La.χ_mem_muImg_iff ⟨y, hyl⟩).1 hp
    exact (hsub this).2.1 rfl
  · obtain ⟨z, hz, hnc⟩ := hFF.exists_not_commute i _ hi _ hp
    have hsmu : (La.χ.symm z : X) ∈ muSet E a b := ⟨(La.χ.symm z).2, La.mem_muImg.1 hz⟩
    have hcomm := (hsub hsmu).2.2
    apply hnc
    have := (La.comm ⟨y, hyl⟩ (La.χ.symm z)).1 hcomm.symm
    rwa [Equiv.apply_symm_apply] at this

theorem Pair.ySet_subset_of_fi22
    {e x : X} (he : e ∈ E) (hx : x ∈ E) (hex : e * x ≠ x * e)
    (hmu : (muSet E e x).Nonempty) : ySet E e x ⊆ {e, x, e * x * e} := by
  have := Pair.finite hE
  rintro y ⟨hyE, hS⟩
  by_cases hye : y = e
  · exact Or.inl hye
  by_cases hyx : y = x
  · exact Or.inr (Or.inl hyx)
  right; right
  have h1 := Pair.not_commute_of_muSet_subset_fi22 hPF hHF hFF hE hloc he hx hex hmu hyE hS hye
  have hxfar : x ∈ farSet E e := ⟨hx, fun h => hex h.symm, hmu⟩
  have hsub : muSet E e x ⊆ muSet E e y := fun s hs => ⟨hs.1, hS hs⟩
  have hyfar : y ∈ farSet E e := ⟨hyE, h1, hmu.mono hsub⟩
  have heq : muSet E e x = muSet E e y := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Pair.ncard_muSet_of_fi22 hPF hHF hFF hE hloc he hyfar,
      Pair.ncard_muSet_of_fi22 hPF hHF hFF hE hloc he hxfar]) (Set.toFinite _)
  obtain ⟨Le⟩ := hloc e he
  have himg : Le.muImg x = Le.muImg y := by
    ext p
    rw [← Equiv.apply_symm_apply Le.χ p, Le.χ_mem_muImg_iff, Le.χ_mem_muImg_iff, heq]
  rcases Le.muImg_fib_of_model hPF f22_J connected_D hE hloc he hxfar hyfar himg with h | h
  · exact absurd h hyx
  · exact h

end Fi22Model

theorem F23.nonempty_compGraphIso'
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    (hE : Pair X E) (hF : Pair Y F)
    (hlocE : ∀ f ∈ E, Nonempty (LocalPoints (pairModel pair_D) E f))
    (hlocF : ∀ f ∈ F, Nonempty (LocalPoints (pairModel pair_D) F f)) {d : X} {d' : Y}
    (hd : d ∈ E) (hd' : d' ∈ F) : Nonempty (compGraph E d ≃g compGraph F d') := by
  obtain ⟨L, hL⟩ := exists_localPoints_lhOrbit_zero hPF hHF hFF hE hlocE hd
  obtain ⟨L', hL'⟩ := exists_localPoints_lhOrbit_zero hPF hHF hFF hF hlocF hd'
  have h := coverHyp_lhOrbit_zero hPF hFF hE hlocE hd L hL
  have h' := coverHyp_lhOrbit_zero hPF hFF hF hlocF hd' L' hL'
  obtain ⟨β, hβπ, hβadj⟩ := TwoCover.exists_iso xi23Root hFF.xi23_D2 hFF.xi23_MU hFF.xi23_ED
    (coverOf hE hd L h) (coverOf hF hd' L' h')
  let βA : farSet E d ≃ farSet F d' := β
  have hπ : ∀ c, L'.muImg (βA c) = L.muImg c := fun c => congrArg Subtype.val (hβπ c)
  exact ⟨compGraphIso hd hd' L L' βA hπ hβadj⟩

theorem F23.nonempty_compGraphIso
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    (hE : F23 X E) (hF : F23 Y F) {d : X} {d' : Y} (hd : d ∈ E) (hd' : d' ∈ F) :
    Nonempty (compGraph E d ≃g compGraph F d') :=
  F23.nonempty_compGraphIso' hPF hHF hFF hE.1 hF.1
    (fun _ hf => F23.nonempty_localPoints_fi22 hPF hE hf)
    (fun _ hf => F23.nonempty_localPoints_fi22 hPF hF hf) hd hd'

theorem F23.exists_mulEquiv
    (hPF : PolarFacts) (hHF : HyperovalFacts) (hFF : Fi22Facts)
    (hE : F23 X E) (hF : F23 Y F) (hZE : Subgroup.center X = ⊥) (hZF : Subgroup.center Y = ⊥)
    (hSE : IsSimpleGroup (commutator X)) (hSF : IsSimpleGroup (commutator Y)) :
    ∃ φ : X ≃* Y, φ '' E = F := by
  have hlocE : ∀ f ∈ E, Nonempty (LocalPoints (pairModel pair_D) E f) :=
    fun _ hf => F23.nonempty_localPoints_fi22 hPF hE hf
  have hlocF : ∀ f ∈ F, Nonempty (LocalPoints (pairModel pair_D) F f) :=
    fun _ hf => F23.nonempty_localPoints_fi22 hPF hF hf
  have hmem : ∀ {Z : Type} [Group Z] {C : Set Z}, Pair Z C →
      (∀ f ∈ C, Nonempty (LocalPoints (pairModel pair_D) C f)) →
      ∃ d ∈ C, ∃ f, f ∈ LocalClass C d := by
    intro Z _ C hP hloc
    obtain ⟨e, he⟩ := hP.2.1
    have hd : e ∈ C := by rw [he]; exact IsConj.refl e
    obtain ⟨L⟩ := hloc e hd
    exact ⟨e, hd, L.χ.symm ⟨a, a_mem_D⟩, (L.χ.symm _).2⟩
  obtain ⟨d, hd, f, hf⟩ := hmem hE.1 hlocE
  obtain ⟨d', hd', f', hf'⟩ := hmem hF.1 hlocF
  have hconnE := Pair.connected_of_simple hE.1 hSE ⟨d, f, hd, hf.1, hf.2.1.symm, hf.2.2.symm⟩
  have hconnF := Pair.connected_of_simple hF.1 hSF ⟨d', f', hd', hf'.1, hf'.2.1.symm, hf'.2.2.symm⟩
  have huE : compSet E d = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hE.1 hconnE hd hc hcd
  have huF : compSet F d' = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty hF.1 hconnF hd' hc hcd
  obtain ⟨ι⟩ := F23.nonempty_compGraphIso hPF hHF hFF hE hF hd hd'
  let β : commGraph E ≃g commGraph F :=
    (compGraphIsoTop huE).symm.trans (ι.trans (compGraphIsoTop huF))
  refine Pair.mulEquiv_of_graphIso hE.1 hF.1 hZE hZF β fun e x he hx hex => ?_
  exact Pair.ySet_subset_of_fi22 hPF hHF hFF hF.1 hlocF he hx hex
    (Pair.muSet_nonempty hF.1 hconnF he hx fun h => hex h.symm)

end CFSG.Fischer
