module

public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusKb
public import CFSG.CGT.PushingUpLit.CGT6.OmegaPlusNatSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

theorem isSubnormal_subgroupOf_map {A B : Type*} [Group A] [Group B] (f : A →* B)
    {H K : Subgroup A} (hHK : H ≤ K) (h : (H.subgroupOf K).IsSubnormal) :
    ((H.map f).subgroupOf (K.map f)).IsSubnormal := by
  have hψ : Function.Surjective (f.subgroupMap K) := f.subgroupMap_surjective K
  have h' := Subgroup.IsSubnormal.map hψ h
  have heq : (H.subgroupOf K).map (f.subgroupMap K) = (H.map f).subgroupOf (K.map f) := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : (f z : B) = y := congrArg Subtype.val hzy
      exact ⟨z, hz, this⟩
    · intro hyH
      obtain ⟨x, hx, hxy⟩ := hyH
      exact ⟨⟨x, hHK hx⟩, hx, Subtype.ext hxy⟩
  rwa [heq] at h'


theorem kgroup_of_surjective {A B : Type} [Group A] [Group B] (hA : CFSG.IsKGroup A) (f : A →* B)
    (hf : Function.Surjective f) : CFSG.IsKGroup B :=
  hA.of_surjective f hf


variable {V : Type} [CommGroup V]

theorem natSL_eq_of_ne_bot {X : Subgroup (MulAut V)} {P : Subgroup V} {n : ℕ}
    (hnat : IsNatSectionBy (slAct n) X P ⊥) {A : Subgroup V} (hAU : A ≤ P)
    (hA : ∀ g ∈ X, ∀ a ∈ A, g a ∈ A) (hne : A ≠ ⊥) : A = P := by
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  obtain ⟨a₀, ha₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha₀U : ((a₀ : ↥A) : V) ∈ P := hAU a₀.2
  have hv₀ : Multiplicative.toAdd (β ⟨(a₀ : V), ha₀U⟩) ≠ 0 := by
    intro h0
    apply ha₀
    have h1 : β ⟨(a₀ : V), ha₀U⟩ = 1 := by
      rw [← ofAdd_toAdd (β _), h0, ofAdd_zero]
    have h2 : (⟨(a₀ : V), ha₀U⟩ : ↥P) = 1 := hβi (h1.trans (map_one β).symm)
    exact Subtype.ext (congrArg (fun y : ↥P => (y : V)) h2)
  refine le_antisymm hAU fun u hu => ?_
  by_cases hv : Multiplicative.toAdd (β ⟨u, hu⟩) = 0
  · have h1 : β ⟨u, hu⟩ = 1 := by rw [← ofAdd_toAdd (β _), hv, ofAdd_zero]
    have h2 : (⟨u, hu⟩ : ↥P) = 1 := hβi (h1.trans (map_one β).symm)
    have h3 : u = 1 := congrArg (fun y : ↥P => (y : V)) h2
    rw [h3]
    exact A.one_mem
  · obtain ⟨g, hg⟩ := Glue.exists_sl2_mulVec_eq_of_ne_zero hv₀ hv
    have hxU : ((θ.symm g : ↥X) : MulAut V) (a₀ : V) ∈ P :=
      hinv _ (θ.symm g).2 _ ha₀U
    have h1 : β ⟨((θ.symm g : ↥X) : MulAut V) (a₀ : V), hxU⟩ = β ⟨u, hu⟩ := by
      refine (hβe (θ.symm g) ⟨(a₀ : V), ha₀U⟩ hxU).trans ?_
      rw [MulEquiv.apply_symm_apply, ← ofAdd_toAdd (β ⟨u, hu⟩)]
      exact congrArg Multiplicative.ofAdd hg
    have h2 := hβi h1
    have h3 : ((θ.symm g : ↥X) : MulAut V) (a₀ : V) = u :=
      congrArg (fun y : ↥P => (y : V)) h2
    rw [← h3]
    exact hA _ (θ.symm g).2 _ a₀.2

theorem natSL_exists_moved {X : Subgroup (MulAut V)} {P : Subgroup V} {n : ℕ}
    (hnat : IsNatSectionBy (slAct n) X P ⊥) : ∃ g ∈ X, ∃ p ∈ P, (g : MulAut V) p ≠ p := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  obtain ⟨p, hp⟩ := hβs (Multiplicative.ofAdd (Pi.single 0 1))
  have hall : ∀ s : SLq n, slAct n s (β p) = β p := by
    intro s
    have h1 := hβe (θ.symm s) p (hinv _ (θ.symm s).2 p p.2)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1]
    congr 1
    exact Subtype.ext (hcon _ (θ.symm s).2 p p.2)
  have h1 := slLift_eq_one_of_fixed (β p) hall
  rw [hp] at h1
  have := congrArg (fun m : Multiplicative (Fin 2 → Fq n) => Multiplicative.toAdd m 0) h1
  simp at this


theorem commVW_invariant {K : Subgroup (MulAut V)} {W : Subgroup V} (hKW : GInv K W) {g : MulAut V}
    (hg : g ∈ K) {u : V} (hu : u ∈ commVW W K) : g u ∈ commVW W K := by
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨k, hk, w, hw, rfl⟩ := hu
    have h1 : g (k w * w⁻¹) = (g * k * g⁻¹) (g w) * (g w)⁻¹ := by
      simp [map_mul, map_inv, MulAut.mul_apply]
    rw [h1]
    exact mem_commVW (K.mul_mem (K.mul_mem hg hk) (K.inv_mem hg)) (hKW g hg w hw)
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem commVW_eq_of_natSL {K : Subgroup (MulAut V)} {E W : Subgroup V} {n : ℕ}
    (hnat : IsNatSectionBy (slAct n) K E ⊥) (hEW : E ≤ W) : E ≤ commVW W K := by
  have hKE : GInv K E := hnat.1
  have hAE : commVW E K ≤ E := commVW_le_W hKE
  have hinv : ∀ g ∈ K, ∀ a ∈ commVW E K, g a ∈ commVW E K := fun g hg a ha =>
    commVW_invariant hKE hg ha
  have hne : commVW E K ≠ ⊥ := by
    obtain ⟨g, hg, p, hp, hne⟩ := natSL_exists_moved hnat
    intro h
    have hmem : (g : MulAut V) p * p⁻¹ ∈ commVW E K := mem_commVW hg hp
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hne hmem
  have := natSL_eq_of_ne_bot hnat hAE hinv hne
  rw [← this]
  exact commVW_mono_W hEW

theorem natSL_faithful {X : Subgroup (MulAut V)} {P : Subgroup V} {n : ℕ}
    (hnat : IsNatSectionBy (slAct n) X P ⊥) {g : MulAut V} (hg : g ∈ X)
    (h : ∀ p ∈ P, g p = p) : g = 1 := by
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  have hall : ∀ m : Multiplicative (Fin 2 → Fq n), slAct n (θ ⟨g, hg⟩) m = m := by
    intro m
    obtain ⟨p, rfl⟩ := hβs m
    rw [← hβe ⟨g, hg⟩ p (hinv g hg p p.2)]
    congr 1
    exact Subtype.ext (h p p.2)
  have h1 : θ ⟨g, hg⟩ = 1 := by
    apply Subtype.ext
    ext i j
    have := congrArg (fun m : Multiplicative (Fin 2 → Fq n) => Multiplicative.toAdd m i)
      (hall (Multiplicative.ofAdd (Pi.single j 1)))
    simp [slAct] at this
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have := θ.injective (h1.trans (map_one θ).symm)
  exact congrArg Subtype.val this


theorem subnormal_of_bar {X D : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv X W)
    (hc : ∀ k ∈ X, (∀ w ∈ W, k w = w) → ∀ d ∈ D, k * d = d * k)
    (hs : ((barW h D).subgroupOf (resG X W h).range).IsSubnormal) :
    (D.subgroupOf X).IsSubnormal := by
  let f : ↥X →* ↥(resG X W h).range := (resG X W h).rangeRestrict
  let N : Subgroup ↥X := ((barW h D).subgroupOf (resG X W h).range).comap f
  have hN : N.IsSubnormal := hs.comap f
  have hmemN : ∀ x : ↥X, x ∈ N → ∃ d : ↥X, (d : MulAut V) ∈ D ∧ resG X W h d = resG X W h x := by
    intro x hx
    have : resG X W h x ∈ barW h D := hx
    obtain ⟨g, hg, hgx⟩ := (mem_barW h).mp this
    exact ⟨g, hg, hgx⟩
  have hDN : D.subgroupOf X ≤ N := by
    intro x hx
    have hxD : (x : MulAut V) ∈ D := hx
    exact (mem_barW h).mpr ⟨x, hxD, rfl⟩
  have hnorm : ((D.subgroupOf X).subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : ((n : ↥X) : MulAut V) ∈ D := hn
    obtain ⟨d, hdD, hdx⟩ := hmemN (g : ↥X) g.2
    have hkfix : ∀ w ∈ W, ((d⁻¹ * (g : ↥X) : ↥X) : MulAut V) w = w := by
      intro w hw
      have h1 : resG X W h (d⁻¹ * (g : ↥X)) = 1 := by
        rw [map_mul, map_inv, hdx, inv_mul_cancel]
      exact (mem_fixW.mp ((mem_ker_resG h).mp (MonoidHom.mem_ker.mpr h1))) w hw
    have hcomm := hc _ (d⁻¹ * (g : ↥X)).2 hkfix ((n : ↥X) : MulAut V) hn'
    have hkey : ((g : ↥X) : MulAut V) * ((n : ↥X) : MulAut V) * ((g : ↥X) : MulAut V)⁻¹ =
        (d : MulAut V) * ((n : ↥X) : MulAut V) * (d : MulAut V)⁻¹ := by
      have hcomm' : ((d : MulAut V)⁻¹ * ((g : ↥X) : MulAut V)) * ((n : ↥X) : MulAut V) =
          ((n : ↥X) : MulAut V) * ((d : MulAut V)⁻¹ * ((g : ↥X) : MulAut V)) := hcomm
      calc ((g : ↥X) : MulAut V) * ((n : ↥X) : MulAut V) * ((g : ↥X) : MulAut V)⁻¹
          = (d : MulAut V) * (((d : MulAut V)⁻¹ * ((g : ↥X) : MulAut V)) * ((n : ↥X) : MulAut V)) *
            ((g : ↥X) : MulAut V)⁻¹ := by group
        _ = (d : MulAut V) * (((n : ↥X) : MulAut V) * ((d : MulAut V)⁻¹ * ((g : ↥X) : MulAut V))) *
            ((g : ↥X) : MulAut V)⁻¹ := by rw [hcomm']
        _ = (d : MulAut V) * ((n : ↥X) : MulAut V) * (d : MulAut V)⁻¹ := by group
    show (((g : ↥X) * (n : ↥X) * (g : ↥X)⁻¹ : ↥X) : MulAut V) ∈ D
    have : (((g : ↥X) * (n : ↥X) * (g : ↥X)⁻¹ : ↥X) : MulAut V) =
        ((g : ↥X) : MulAut V) * ((n : ↥X) : MulAut V) * ((g : ↥X) : MulAut V)⁻¹ := rfl
    rw [this, hkey]
    exact D.mul_mem (D.mul_mem hdD hn') (D.inv_mem hdD)
  exact Subgroup.IsSubnormal.trans hDN hnorm.isSubnormal hN


section Cent

variable [Finite V] {G : Subgroup (MulAut V)} {b : MulAut V}

omit [Finite V] in
theorem ginv_cent (G : Subgroup (MulAut V)) (b : MulAut V) :
    GInv (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V))) (fixV (Subgroup.zpowers b)) := by
  intro g hg w hw
  have hbg : b * g = g * b := Subgroup.mem_centralizer_iff.mp hg.2 b rfl
  apply Quasithin.mem_fixV_zpowers_iff.mpr
  have h1 : b w = w := Quasithin.mem_fixV_zpowers_iff.mp hw
  have h2 := congrArg (fun z : MulAut V => z w) hbg
  simp only [MulAut.mul_apply] at h2
  rw [h2, h1]

omit [Finite V] in
theorem mem_ker_cent (g : ↥(G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))) :
    g ∈ (resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V))) (fixV (Subgroup.zpowers b))
      (ginv_cent G b)).ker ↔ (g : MulAut V) ∈ kStab G b := by
  rw [mem_ker_resG, mem_kStab, mem_fixW]
  have hgb : (g : MulAut V) * b = b * (g : MulAut V) := by
    have := Subgroup.mem_centralizer_iff.mp g.2.2 b rfl
    exact this.symm
  exact ⟨fun hf => ⟨⟨g.2.1, hgb⟩, hf⟩, fun hf => hf.2⟩


omit [Finite V] in
theorem commutator_subgroupOf_perfect {N Y : Subgroup (MulAut V)} (hYN : Y ≤ N)
    (hperf : ⁅Y, Y⁆ = Y) : ⁅Y.subgroupOf N, Y.subgroupOf N⁆ = Y.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hYN, hperf]

omit [Finite V] in
theorem barW_perfect {X D : Subgroup (MulAut V)} {W : Subgroup V} (h : GInv X W) (hDX : D ≤ X)
    (hD : ⁅D, D⁆ = D) : ⁅barW h D, barW h D⁆ = barW h D := by
  unfold barW
  rw [← Subgroup.map_commutator, commutator_subgroupOf_perfect hDX hD]

theorem card_xbar_lt {G : Subgroup (MulAut V)} {b : MulAut V} (hbG : b ∈ G) (hb1 : b ≠ 1) :
    Nat.card ↥(resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V))) (fixV (Subgroup.zpowers b))
      (ginv_cent G b)).range < Nat.card ↥G := by
  set X := G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) with hX
  set f := resG X (fixV (Subgroup.zpowers b)) (ginv_cent G b) with hf
  have hbX : b ∈ X := ⟨hbG, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]⟩
  have hbk : (⟨b, hbX⟩ : ↥X) ∈ f.ker := by
    rw [mem_ker_resG]
    intro w hw
    exact Quasithin.mem_fixV_zpowers_iff.mp hw
  have hcard : Nat.card ↥f.range * Nat.card ↥f.ker = Nat.card ↥X := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : 2 ≤ Nat.card ↥f.ker := by
    have : Nontrivial ↥f.ker := ⟨⟨⟨⟨b, hbX⟩, hbk⟩, 1, fun h => hb1 (by
      have := congrArg (fun z : ↥f.ker => ((z : ↥X) : MulAut V)) h
      simpa using this)⟩⟩
    exact Nat.succ_le_of_lt Finite.one_lt_card
  have hXG : Nat.card ↥X ≤ Nat.card ↥G := Subgroup.card_le_of_le inf_le_left
  have hpos : 0 < Nat.card ↥f.range := Nat.card_pos
  nlinarith

omit [Finite V] in
theorem isKGroup_xbar {G : Subgroup (MulAut V)} {b : MulAut V} (hG : CFSG.IsKGroup ↥G) :
    CFSG.IsKGroup ↥(resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))
      (fixV (Subgroup.zpowers b)) (ginv_cent G b)).range :=
  kgroup_of_surjective (isKGroup_of_le hG inf_le_left)
    (resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V))) (fixV (Subgroup.zpowers b))
      (ginv_cent G b)).rangeRestrict (MonoidHom.rangeRestrict_surjective _)

omit [Finite V] in
theorem barW_cent_eq {G : Subgroup (MulAut V)} {b t : MulAut V}
    (htX : t ∈ G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)))
    (hB : ∀ x ∈ G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)),
      x * t * x⁻¹ * t⁻¹ ∈ kStab G b → x * t = t * x) :
    barW (ginv_cent G b) (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) ⊓
        Subgroup.centralizer ({t} : Set (MulAut V))) =
      (resG (G ⊓ Subgroup.centralizer ({b} : Set (MulAut V))) (fixV (Subgroup.zpowers b))
        (ginv_cent G b)).range ⊓
      Subgroup.centralizer ((barW (ginv_cent G b) (Subgroup.zpowers t) :
        Subgroup (MulAut ↥(fixV (Subgroup.zpowers b)))) :
          Set (MulAut ↥(fixV (Subgroup.zpowers b)))) := by
  set X := G ⊓ Subgroup.centralizer ({b} : Set (MulAut V)) with hX
  have h := ginv_cent G b
  set r := resG X (fixV (Subgroup.zpowers b)) h with hr
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, rfl⟩ := (mem_barW h).mp hy
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    obtain ⟨s, hs, rfl⟩ := (mem_barW h).mp hz
    have hgt' : Commute t (g : MulAut V) := Subgroup.mem_centralizer_iff.mp hg.2 t rfl
    have hgt : Commute (g : MulAut V) t := hgt'.symm
    have hcomm : (s : MulAut V) * (g : MulAut V) = (g : MulAut V) * (s : MulAut V) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      rw [← hk]
      exact ((hgt.zpow_right k).eq).symm
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  · rintro ⟨⟨x, rfl⟩, hy⟩
    have hmem : r ⟨t, htX⟩ ∈ barW h (Subgroup.zpowers t) :=
      resG_mem_barW h (Subgroup.mem_zpowers t)
    have hc : r ⟨t, htX⟩ * r x = r x * r ⟨t, htX⟩ := Subgroup.mem_centralizer_iff.mp hy _ hmem
    have hk : x * ⟨t, htX⟩ * x⁻¹ * ⟨t, htX⟩⁻¹ ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      calc r x * r ⟨t, htX⟩ * (r x)⁻¹ * (r ⟨t, htX⟩)⁻¹ =
          (r ⟨t, htX⟩ * r x) * (r x)⁻¹ * (r ⟨t, htX⟩)⁻¹ := by rw [hc]
        _ = 1 := by group
    have hkb := hB x x.2 ((mem_ker_cent _).mp hk)
    refine (mem_barW h).mpr ⟨x, ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.mp hz]
    exact hkb.symm

end Cent

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
