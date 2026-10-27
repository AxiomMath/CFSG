module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G : Type*} [Group G]

theorem rightCoset_fixed_iff (H P : Subgroup G) (omega : pointRightCosetSpace H) :
    omega ∈ pointFixedSet H P ↔
      ∀ p ∈ P, p • QuotientGroup.quotientRightRelEquivQuotientLeftRel H omega =
        QuotientGroup.quotientRightRelEquivQuotientLeftRel H omega := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  constructor
  · intro h p hp
    have hinv := h p⁻¹ (P.inv_mem hp)
    have heq := congrArg e hinv
    simpa only [pointRightCosetMul, e, Equiv.apply_symm_apply, inv_inv] using heq
  · intro h p hp
    apply e.injective
    have hinv := h p⁻¹ (P.inv_mem hp)
    simpa only [pointRightCosetMul, e, Equiv.apply_symm_apply] using hinv

theorem rightCoset_fixed_card (H P : Subgroup G) :
    Nat.card (pointFixedSet H P) =
      Nat.card {omega : G ⧸ H // ∀ p ∈ P, p • omega = omega} := by
  apply Nat.card_congr
  exact (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).subtypeEquiv
    (fun omega => rightCoset_fixed_iff H P omega)

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
