module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldTransfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldVector
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups IsMulCommutative

variable {F : Type u} [Field F]

theorem elementary_outer_order (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (a : Gamma F) (ha : a ∈ A) (houter : a ∉ linearKernel F) : orderOf a = 2 := by
  apply orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian a ha)
  intro hone
  exact houter (hone ▸ (linearKernel F).one_mem)

theorem original_elementary_quotient_card [Finite F] {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (houter : ¬A ≤ linearKernel F) : Nat.card (A ⧸ linearIntersection A) = 2 := by
  let : IsCyclic (RingAut F) := (ringAut_card_and_cyclic hcard).2
  exact outer_elementary_quotient_card A houter

theorem original_outer_elementary_card_and_rank [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (A : Subgroup (Gamma F)) [CFSG.IsElementaryAbelian 2 A]
    (a : Gamma F) (ha : a ∈ A) (houter : a ∉ linearKernel F) :
    ∃ s : ℕ, 1 ≤ s ∧ n = 2 * s ∧
      (∀ c : F, a.right c = c ^ (2 ^ s)) ∧
      Nat.card (fixedField a.right) = 2 ^ s ∧
      Nat.card (A ⧸ linearIntersection A) = 2 ∧
      Nat.card A = 2 * Nat.card (linearIntersection A) ∧
      Nat.card (linearIntersection A) ≤ 2 ^ s ∧
      Nat.card A ≤ 2 ^ (s + 1) ∧
      Module.finrank (ZMod 2) (Additive (linearIntersection A)) ≤ s ∧
      Module.finrank (ZMod 2) (Additive (intersectionS A)) ≤ s ∧
      Module.finrank (ZMod 2) (Additive A) ≤ s + 1 := by
  let : CharP F 2 := char_two_of_card hcard
  let : IsCyclic (RingAut F) := (ringAut_card_and_cyclic hcard).2
  have hAouter : ¬A ≤ linearKernel F := fun hle => houter (hle ha)
  have haorder := elementary_outer_order A a ha houter
  obtain ⟨hane, hapow, _hacocycle⟩ := outer_involution_cocycle a haorder houter
  obtain ⟨s, hs, hns, hfrob, hfixed⟩ := finite_field_involution_exact hn hcard
    a.right hapow hane
  have hS : Nat.card (intersectionS A) ≤ 2 ^ s := by
    rw [← hfixed]
    exact pgroup_outer_centralizer_card_le a haorder houter (intersectionS A)
      (intersectionS_isPGroup A) (intersectionS_le_centralizer A a ha)
  have hI : Nat.card (linearIntersection A) ≤ 2 ^ s := by
    rw [linearIntersection_card_eq_intersectionS]
    exact hS
  have hfactor := outer_elementary_card_factor A hAouter
  have hA : Nat.card A ≤ 2 ^ (s + 1) := by
    calc
      Nat.card A = 2 * Nat.card (linearIntersection A) := hfactor
      _ ≤ 2 * 2 ^ s := Nat.mul_le_mul_left 2 hI
      _ = 2 ^ (s + 1) := by rw [pow_succ, Nat.mul_comm]
  exact ⟨s, hs, hns, hfrob, hfixed, outer_elementary_quotient_card A hAouter,
    hfactor, hI, hA, elementary_finrank_le_of_card_le hI,
    elementary_finrank_le_of_card_le hS, elementary_finrank_le_of_card_le hA⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
