module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem pointFixedSet_rightConjugate_mem (H Q : Subgroup G) (n : G)
    {a : pointRightCosetSpace H} (ha : a ∈ pointFixedSet H Q) :
    pointRightCosetMul H a n ∈ pointFixedSet H (rightConjugate Q n) := by
  intro q hq
  have hconj := (mem_right_conjugate_iff Q n q).mp hq
  calc
    pointRightCosetMul H (pointRightCosetMul H a n) q =
        pointRightCosetMul H a (n * q) := pointRightCosetMul_mul H a n q
    _ = pointRightCosetMul H (pointRightCosetMul H a (n * q * n⁻¹)) n := by
      rw [pointRightCosetMul_mul]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    _ = pointRightCosetMul H a n := by rw [ha _ hconj]

@[expose] def pointFixedSetRightConjugateEquiv (H Q : Subgroup G) (n : G) :
    pointFixedSet H Q ≃ pointFixedSet H (rightConjugate Q n) where
  toFun a := ⟨pointRightCosetMul H a.val n,
    pointFixedSet_rightConjugate_mem H Q n a.property⟩
  invFun a := ⟨pointRightCosetMul H a.val n⁻¹, by
    intro q hq
    have hconj : n⁻¹ * q * n ∈ rightConjugate Q n := by
      apply (mem_right_conjugate_iff Q n _).mpr
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hq
    calc
      pointRightCosetMul H (pointRightCosetMul H a.val n⁻¹) q =
          pointRightCosetMul H a.val (n⁻¹ * q) := pointRightCosetMul_mul H a.val n⁻¹ q
      _ = pointRightCosetMul H (pointRightCosetMul H a.val (n⁻¹ * q * n)) n⁻¹ := by
        rw [pointRightCosetMul_mul]
        simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = pointRightCosetMul H a.val n⁻¹ := by rw [a.property _ hconj]⟩
  left_inv a := by
    apply Subtype.ext
    simp only [pointRightCosetMul_mul, mul_inv_cancel, pointRightCosetMul_one]
  right_inv a := by
    apply Subtype.ext
    simp only [pointRightCosetMul_mul, inv_mul_cancel, pointRightCosetMul_one]

theorem pointFixedSet_rightConjugate_card (H Q : Subgroup G) (n : G) :
    Nat.card (pointFixedSet H (rightConjugate Q n)) = Nat.card (pointFixedSet H Q) :=
  (Nat.card_congr (pointFixedSetRightConjugateEquiv H Q n)).symm

theorem two_le_pointFixedSet_card_of_pair [Finite G]
    (H Q : Subgroup G) (a b : pointRightCosetSpace H) (hab : a ≠ b)
    (ha : a ∈ pointFixedSet H Q) (hb : b ∈ pointFixedSet H Q) :
    2 ≤ Nat.card (pointFixedSet H Q) := by
  have hsub : ({a, b} : Set (pointRightCosetSpace H)) ⊆ pointFixedSet H Q := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hab] at hc
  exact hc

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
