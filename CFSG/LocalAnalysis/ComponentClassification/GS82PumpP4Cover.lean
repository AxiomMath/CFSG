module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP4Lift
public import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt
open scoped MatrixGroups

theorem odd_exceptionalOrders_PSU {m p f : ℕ} (hp2 : p ≠ 2) :
    Odd ((exceptionalOrders .PSU m p f).1 * (exceptionalOrders .PSU m p f).2) := by
  have h : Odd (exceptionalOrders .PSU m p f).1 ∧ Odd (exceptionalOrders .PSU m p f).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    all_goals decide
  exact h.1.mul h.2

theorem exists_scalar_cover {m : ℕ} {K : Type} [Field K] [Finite K]
    {H : Subgroup (GL (Fin m) K)} (hH : Group.IsPerfect ↥H)
    {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y) (h2 : IsPGroup 2 ↥(center Y))
    (e : Y ⧸ center Y ≃* StatedProj H) {o : ℕ} (ho : Odd o)
    (hM : Nat.card (RankThree.PerfectCover.hopfMultiplier (StatedProj H)) =
      Nat.card ↥((StatedScalars (Fin m) K).subgroupOf H) * o) :
    ∃ π : ↥H →* Y, Function.Surjective π ∧
      ∀ g, g ∈ (StatedScalars (Fin m) K).subgroupOf H ↔ π g ∈ center Y := by
  obtain ⟨α, hαs, hαc⟩ := GH74.Generic.exists_lift_of_odd_index hH hY.1
    (QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf H)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact Open.StatedAPI.statedScalars_subgroupOf_le_center H)
    (GH74.Generic.centralQuotientMap e) (GH74.Generic.centralQuotientMap_surjective e)
    (GH74.Generic.centralQuotientMap_ker e).le
    (by rw [GH74.Generic.centralQuotientMap_ker e]; exact h2) o ho
    (by rw [hM, QuotientGroup.ker_mk'])
  refine ⟨α, hαs, fun g => ?_⟩
  have h1 : GH74.Generic.centralQuotientMap e (α g) = QuotientGroup.mk g := by
    have := DFunLike.congr_fun hαc g
    simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] using this
  rw [← QuotientGroup.eq_one_iff g, ← h1, ← MonoidHom.mem_ker, GH74.Generic.centralQuotientMap_ker]

theorem exists_psl_cover
    {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y) (h2 : IsPGroup 2 ↥(center Y))
    {m p f : ℕ} (hp2 : p ≠ 2) (hcl : StatedClassicalModel (Y ⧸ center Y) .PSL m p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSL m K) →* Y),
      Function.Surjective π ∧
      (∀ g, g ∈ (StatedScalars (Fin m) K).subgroupOf (StatedSL m K) ↔ π g ∈ center Y) ∧
      ordProj[2] (Nat.card ↥((StatedScalars (Fin m) K).subgroupOf (StatedSL m K))) =
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y))) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hcl
  obtain ⟨hp, hf, hm2, h22, h23⟩ := hadm
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h4 : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4 := by
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
    · right
      apply SL2Closed.exists_four_of_five_le
      have hq2 : p ^ f ≠ 2 := fun h => h22 (by rw [h])
      have hq3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
      have hq1 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
      obtain ⟨k, hk⟩ := hq
      rw [hK]
      omega
    · exact .inl h3
  have hSL : Group.IsPerfect SL(m, K) := LinearGroups.special_linear_isPerfect hm2 h4
  have hH : Group.IsPerfect ↥(StatedSL m K) :=
    Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL m K).toMonoidHom)
      (MulEquiv.surjective _)
  obtain ⟨-, ⟨eM⟩⟩ := GriessClassical.psl_row (X := StatedProj (StatedSL m K))
    ⟨⟨hp, hf, hm2, h22, h23⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hexc := odd_exceptionalOrders_PSL (m := m) (f := f) hp2
  have hN : Nat.card ↥((StatedScalars (Fin m) K).subgroupOf (StatedSL m K)) =
      Nat.gcd m (p ^ f - 1) := by
    rw [← map_center_eq_statedScalars m K,
      Subgroup.card_map_of_injective (specialLinearGroupEquivStatedSL m K).injective,
      OrderReductions.LinearOrders.card_specialLinear_center K m (by omega), hK]
  have hMcard : Nat.card (RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSL m K))) =
      Nat.card ↥((StatedScalars (Fin m) K).subgroupOf (StatedSL m K)) *
        ((exceptionalOrders .PSL m p f).1 * (exceptionalOrders .PSL m p f).2) := by
    rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_prod, hN]
    unfold generic exceptional
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
    simp [genericOrders]
  obtain ⟨π, hπ, hπN⟩ := exists_scalar_cover hH hY h2 e hexc hMcard
  refine ⟨K, inferInstance, inferInstance, π, hπ, hπN, ?_⟩
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv, hMcard,
    ordProj_two_mul_odd Nat.card_pos.ne' hexc]

theorem exists_psu_cover
    {Y : Type} [Group Y] [Finite Y] (hY : IsQuasisimple Y) (h2 : IsPGroup 2 ↥(center Y))
    {m p f : ℕ} (hp2 : p ≠ 2) (hm : Even m)
    (hcl : StatedClassicalModel (Y ⧸ center Y) .PSU m p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSU m (p ^ f) K) →* Y),
      Function.Surjective π ∧
      (∀ g, g ∈ (StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K) ↔
        π g ∈ center Y) ∧
      ordProj[2] (Nat.card ↥((StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K))) =
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (Y ⧸ center Y))) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hcl
  obtain ⟨hp, hf, hm3, hm32⟩ := hadm
  have : Fact p.Prime := ⟨hp⟩
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hH : Group.IsPerfect ↥(StatedSU m (p ^ f) K) :=
    ClassicalGroups.Unitary.isPerfect_statedSU hK hm3 hm32
  have hcl' : StatedClassicalModel (StatedProj (StatedSU m (p ^ f) K)) .PSU m p f :=
    ⟨⟨hp, hf, hm3, hm32⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hrow : Nonempty (Open.griessHopfMultiplier (StatedProj (StatedSU m (p ^ f) K)) ≃*
      generic .PSU m p f × exceptional .PSU m p f) := by
    by_cases h3 : p ^ f = 3 ∧ m = 4
    · obtain ⟨h3, rfl⟩ := h3
      obtain ⟨rfl, rfl⟩ := GriessClassical.GriessExceptionalPow.eq_three_one_of_pow_eq_three hp
        (by omega) h3
      exact (GriessClassical.psu_four_three_row ⟨hcl'.1, .inl hcl'⟩).2
    · refine (GriessClassical.psu_row hcl' hm ?_).2
      have hq1 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
      obtain ⟨k, hk⟩ := hq
      obtain ⟨j, hj⟩ := hm
      by_cases hq3 : p ^ f = 3
      · exact .inr (.inr ⟨hq3, by omega⟩)
      · exact .inl (by omega)
  obtain ⟨eM⟩ := hrow
  have hexc := odd_exceptionalOrders_PSU (m := m) (f := f) hp2
  have hN : Nat.card ↥((StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K)) =
      Nat.gcd m (p ^ f + 1) := (LinearGroups.unitary_scalar_kernel hp hK (by omega)).2.2
  have hMcard :
      Nat.card (RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSU m (p ^ f) K))) =
        Nat.card ↥((StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K)) *
          ((exceptionalOrders .PSU m p f).1 * (exceptionalOrders .PSU m p f).2) := by
    rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_prod, hN]
    unfold generic exceptional
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
    simp [genericOrders]
  obtain ⟨π, hπ, hπN⟩ := exists_scalar_cover hH hY h2 e hexc hMcard
  refine ⟨K, inferInstance, inferInstance, π, hπ, hπN, ?_⟩
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv, hMcard,
    ordProj_two_mul_odd Nat.card_pos.ne' hexc]

theorem eq_of_mem_statedScalars {n : ℕ} [NeZero n] {F : Type} [Field F]
    {H : Subgroup (GL (Fin n) F)} {x y : ↥H} (hx : x ∈ (StatedScalars (Fin n) F).subgroupOf H)
    (hy : y ∈ (StatedScalars (Fin n) F).subgroupOf H) (hxx : x * x = 1) (hyy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have key : ∀ u : ↥H, u ∈ (StatedScalars (Fin n) F).subgroupOf H → u * u = 1 → u ≠ 1 →
      (u : GL (Fin n) F) = Matrix.GeneralLinearGroup.scalar (Fin n) (-1) := by
    intro u hu huu hu1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hu
    have hc' : (c : F) * (c : F) = 1 := by
      have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin n) (c * c) : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) 0 0 = 1 := by
        rw [map_mul, hc, ← Subgroup.coe_mul, huu, Subgroup.coe_one, Units.val_one,
          Matrix.one_apply_eq]
      simpa [Matrix.GeneralLinearGroup.coe_scalar] using h1
    rcases mul_self_eq_one_iff.mp hc' with h1 | h1
    · exfalso
      apply hu1
      apply Subtype.ext
      rw [← hc, Subgroup.coe_one, show c = 1 from Units.ext h1, map_one]
    · rw [← hc, show c = -1 from Units.ext (by simpa using h1)]
  exact Subtype.ext ((key x hx hxx hx1).trans (key y hy hyy hy1).symm)

theorem card_center_eq_of_scalar_cover
    {Y : Type} [Group Y] [Finite Y] (h2 : IsPGroup 2 ↥(center Y))
    {m : ℕ} [NeZero m] {K : Type} [Field K] [Finite K] {H : Subgroup (GL (Fin m) K)}
    (π : ↥H →* Y) (hπ : Function.Surjective π)
    (hπN : ∀ g, g ∈ (StatedScalars (Fin m) K).subgroupOf H ↔ π g ∈ center Y)
    {A : Subgroup Y} {q₀ : ℕ} (hq₀ : Odd q₀) (h5 : 5 ≤ q₀)
    (hA : HarrisLit.IsSLTwoOver q₀ (↥A ⧸ pPrimeCore 2 ↥A))
    {c : Y} (hcA : c ∈ A) (hcZ : c ∈ center Y) (hcc : c * c = 1) (hc1 : c ≠ 1) :
    Nat.card ↥(center Y) = ordProj[2] (Nat.card ↥((StatedScalars (Fin m) K).subgroupOf H)) := by
  set E := A.comap π with hE
  let ρ : ↥E →* ↥A := (π.comp E.subtype).codRestrict A fun x => x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨g, rfl⟩ := hπ a
    exact ⟨⟨g, ha⟩, rfl⟩
  have hker : ρ.ker ≤ center ↥E := by
    intro x hx
    have h1 : π (x : ↥H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : ↥H) ∈ center ↥H :=
      Open.StatedAPI.statedScalars_subgroupOf_le_center H ((hπN _).mpr (by
        rw [h1]
        exact one_mem _))
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp h2 g)
  have hcA' : (⟨c, hcA⟩ : ↥A) ∈ center ↥A :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp hcZ g)
  obtain ⟨t, htt, hρt⟩ := exists_involution_lift ρ hρ hker hq₀ h5 hA hcA' (Subtype.ext hcc)
  have hπt : π (t : ↥H) = c := congrArg Subtype.val hρt
  exact card_center_eq_ordProj_of_cover π hπ hπN
    (fun x hx y hy hxx hyy hx1 hy1 => eq_of_mem_statedScalars hx hy hxx hyy hx1 hy1)
    h2 (t := (t : ↥H)) (congrArg Subtype.val htt) (hπt ▸ hcZ) (hπt ▸ hc1)

end CFSG.ComponentClassification.GS82PumpInputs.P4
