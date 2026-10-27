module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.QuasithinUnique.Lin2

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBSymplecticTwo (kernel_generation)
open CFSG.QuasithinUnique.Lin2.Five

theorem inner_le_E {F : Type} [Field F] :
    inner (StatedProj (StatedSp 2 F)) ≤ spSemilinearAutGroup 2 F := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [← conjAut_statedSp]
  exact spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup _)

theorem sp4OutCyclic : Sp4OutCyclic := by
  intro F _ _ e hF he
  have hcard : Nat.card F = 2 ^ e := by rw [Nat.card_eq_fintype_card, hF]
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two he hcard
  obtain ⟨φ, hφ, hord, hgen, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two he hcard
  have hφfrob : φ = frobAut F := RingEquiv.ext fun a => by rw [hφ, frobAut_apply]
  have hτE : (tauAut : MulAut (StatedProj (StatedSp 2 F))) ∉ spSemilinearAutGroup 2 F :=
    tauAut_not_mem_E
  have hτ2 : (tauAut : MulAut (StatedProj (StatedSp 2 F))) * tauAut = fieldAut 2 F φ := by
    rw [hφfrob]
    exact tauAut_mul_self
  have hDI : (inner (StatedProj (StatedSp 2 F))).relIndex (spLinearAutGroup 2 F) = 1 := by
    have h := relIndex_inner_spLinearAutGroup_dvd (r := 2) (K := F) Nat.prime_two he hcard
    have hgcd : Nat.gcd 2 (2 ^ e - 1) = 1 := by
      have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
      obtain ⟨k, hk⟩ : Even (2 ^ e) := Nat.even_pow.mpr ⟨even_two, he.ne'⟩
      exact Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
    rw [hgcd] at h
    exact Nat.dvd_one.mp h
  have hDle : spLinearAutGroup 2 F ≤ inner (StatedProj (StatedSp 2 F)) :=
    Subgroup.relIndex_eq_one.mp hDI
  obtain ⟨-, -, -, hEidx⟩ := kernel_generation (K := F)
  have hEne : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hEne1 : (spSemilinearAutGroup 2 F).index ≠ 1 := fun h1 => hτE (by
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _)
  have hE2 : (spSemilinearAutGroup 2 F).index = 2 := by omega
  obtain ⟨π, hπ⟩ : ∃ π : MulAut (StatedProj (StatedSp 2 F)) →*
      Outer (StatedProj (StatedSp 2 F)), ∀ α, π α = (α : Outer (StatedProj (StatedSp 2 F))) :=
    ⟨QuotientGroup.mk' _, fun _ => rfl⟩
  have hπ1 : ∀ α : MulAut (StatedProj (StatedSp 2 F)), π α = 1 →
      α ∈ inner (StatedProj (StatedSp 2 F)) := fun α h =>
    (QuotientGroup.eq_one_iff α).mp (by rw [← hπ]; exact h)
  have hπ2 : ∀ α ∈ inner (StatedProj (StatedSp 2 F)), π α = 1 := fun α h => by
    rw [hπ]
    exact (QuotientGroup.eq_one_iff α).mpr h
  have hπs : ∀ y : Outer (StatedProj (StatedSp 2 F)),
      ∃ α : MulAut (StatedProj (StatedSp 2 F)), π α = y := fun y => by
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨α, hπ α⟩
  have hτ2E : tauAut * tauAut ∈ spSemilinearAutGroup 2 F := by
    rw [hτ2]
    exact fieldAut_mem_spSemilinearAutGroup φ
  have hE : ∀ α ∈ spSemilinearAutGroup 2 F, ∃ k : ℤ, π α = (π tauAut * π tauAut) ^ k := by
    intro α hα
    obtain ⟨σ, hσ⟩ := exists_fieldAut_inv_mul_mem hα
    have hσ' : σ ∈ Subgroup.zpowers φ := by rw [hgen]; exact Subgroup.mem_top _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ'
    refine ⟨k, ?_⟩
    have h1 : π ((fieldAut 2 F (φ ^ k))⁻¹ * α) = 1 := hπ2 _ (hDle hσ)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1, map_zpow, map_zpow, ← hτ2, map_mul]
  have hmem2 : π tauAut * π tauAut ∈ Subgroup.zpowers (π tauAut) :=
    mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have htop : Subgroup.zpowers (π tauAut) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨α, rfl⟩ := hπs y
    by_cases hα : α ∈ spSemilinearAutGroup 2 F
    · obtain ⟨k, hk⟩ := hE α hα
      rw [hk]
      exact Subgroup.zpow_mem _ hmem2 k
    · have hτα : tauAut⁻¹ * α ∈ spSemilinearAutGroup 2 F :=
        (Subgroup.mul_mem_iff_of_index_two hE2).mpr
          ⟨fun h => absurd (inv_mem_iff.mp h) hτE, fun h => absurd h hα⟩
      obtain ⟨k, hk⟩ := hE _ hτα
      have hα' : π α = π tauAut * (π tauAut * π tauAut) ^ k := by
        rw [← hk, ← map_mul, mul_inv_cancel_left]
      rw [hα']
      exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.zpow_mem _ hmem2 k)
  refine ⟨isCyclic_iff_exists_zpowers_eq_top.mpr ⟨π tauAut, htop⟩, ?_⟩
  rw [← orderOf_eq_card_of_zpowers_eq_top htop]
  have hdvd : orderOf (π tauAut) ∣ 2 * e := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_mul, pow_two, hτ2, ← map_pow, ← hord, pow_orderOf_eq_one, map_one, map_one]
  have hmul : 2 * e ∣ orderOf (π tauAut) := by
    have hinner : tauAut ^ orderOf (π tauAut) ∈ inner (StatedProj (StatedSp 2 F)) :=
      hπ1 _ (by rw [map_pow]; exact pow_orderOf_eq_one _)
    rcases Nat.even_or_odd' (orderOf (π tauAut)) with ⟨j, hj | hj⟩
    · rw [hj] at hinner
      have h2 : fieldAut 2 F (φ ^ j) ∈ inner (StatedProj (StatedSp 2 F)) := by
        rw [map_pow, ← hτ2, ← pow_two, ← pow_mul]
        exact hinner
      have h3 : φ ^ j = 1 := fieldAut_eq_one_of_mem_inner h2
      have h4 : e ∣ j := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one h3
      rw [hj]
      exact Nat.mul_dvd_mul_left 2 h4
    · exfalso
      apply hτE
      rw [hj] at hinner
      have h6 : (tauAut * tauAut) ^ j ∈ spSemilinearAutGroup 2 F := pow_mem hτ2E j
      have h7 : (tauAut : MulAut (StatedProj (StatedSp 2 F))) =
          ((tauAut * tauAut) ^ j)⁻¹ * tauAut ^ (2 * j + 1) := by
        rw [pow_succ, pow_mul, pow_two, inv_mul_cancel_left]
      rw [h7]
      exact mul_mem (inv_mem h6) (inner_le_E hinner)
  exact Nat.dvd_antisymm hdvd hmul

end CFSG.QuasithinUnique.Lin2
