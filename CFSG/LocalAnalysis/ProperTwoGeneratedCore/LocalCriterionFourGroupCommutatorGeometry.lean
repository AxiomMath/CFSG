module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorDecomposition
import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open CFSG

universe u v

variable {A : Type u} [Group A] [Finite A] [IsKleinFour A]
variable {I : Type v} [Group I] [MulDistribMulAction A I]

theorem common_fixed_eq_two (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    fixedPointSubgroup A I = actorFixedSubgroup a ⊓ actorFixedSubgroup b := by
  classical
  let : Fintype A := Fintype.ofFinite A
  ext x
  constructor
  · intro hx
    exact ⟨hx a, hx b⟩
  · rintro ⟨hxa, hxb⟩ c
    change a • x = x at hxa
    change b • x = x at hxb
    have hcases : c = a * b ∨ c = a ∨ c = b ∨ c = 1 := by
      have hc : c ∈ ({a * b, a, b, (1 : A)} : Finset A) := by
        rw [IsKleinFour.eq_finset_univ ha hb hab]
        exact Finset.mem_univ c
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    rcases hcases with hc | hc | hc | hc
    · rw [hc, mul_smul, hxb, hxa]
    · exact hc ▸ hxa
    · exact hc ▸ hxb
    · rw [hc, one_smul]

theorem four_group_single_fixed_factorization [Finite I]
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) (x : I) (hx : x ∈ actorFixedSubgroup a) :
    ∃ c ∈ fixedPointSubgroup A I,
      ∃ r ∈ actorCommutatorSubgroup b (actorFixedSubgroup a), x = c * r := by
  let : IsMulCommutative A := IsKleinFour.isMulCommutative
  let : CFSG.IsInvariant A I (actorFixedSubgroup (I := I) a) :=
    actorFixedSubgroup_invariant a
  obtain ⟨c, hc, r, hr, hcf, hprod⟩ :=
    odd_involution_fixed_commutator_factorization hodd b (IsKleinFour.mul_self b)
      (actorFixedSubgroup a) x hx
  refine ⟨c, ?_, r, hr, hprod⟩
  rw [common_fixed_eq_two a b ha hb hab]
  exact ⟨hc, hcf⟩

theorem four_group_two_fixed_covers [Finite I]
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (hodd : Odd (Nat.card I)) :
    let K := actorCommutatorSubgroup b (actorFixedSubgroup (I := I) a) ⊔
      actorCommutatorSubgroup b (actorFixedSubgroup (I := I) (a * b))
    (∀ x ∈ actorFixedSubgroup (I := I) a,
      ∃ c ∈ fixedPointSubgroup A I, ∃ r ∈ K, x = c * r) ∧
    (∀ x ∈ actorFixedSubgroup (I := I) (a * b),
      ∃ c ∈ fixedPointSubgroup A I, ∃ r ∈ K, x = c * r) := by
  dsimp only
  constructor
  · intro x hx
    obtain ⟨c, hc, r, hr, hprod⟩ :=
      four_group_single_fixed_factorization a b ha hb hab hodd x hx
    exact ⟨c, hc, r,
      (show actorCommutatorSubgroup b (actorFixedSubgroup (I := I) a) ≤
        actorCommutatorSubgroup b (actorFixedSubgroup a) ⊔
          actorCommutatorSubgroup b (actorFixedSubgroup (a * b)) from le_sup_left) hr,
      hprod⟩
  · intro x hx
    have hab1 : a * b ≠ 1 := by
      intro h
      exact hab ((mul_eq_one_iff_eq_inv.mp h).trans (IsKleinFour.inv_eq_self b))
    have habb : a * b ≠ b := by
      intro h
      exact ha (mul_right_cancel (show a * b = 1 * b by simpa using h))
    obtain ⟨c, hc, r, hr, hprod⟩ :=
      four_group_single_fixed_factorization (a * b) b hab1 hb habb hodd x hx
    exact ⟨c, hc, r,
      (show actorCommutatorSubgroup b (actorFixedSubgroup (I := I) (a * b)) ≤
        actorCommutatorSubgroup b (actorFixedSubgroup a) ⊔
          actorCommutatorSubgroup b (actorFixedSubgroup (a * b)) from le_sup_right) hr,
      hprod⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
