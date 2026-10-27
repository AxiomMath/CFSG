module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSParts

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS



@[expose] def ResidualCFrameSmall : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) →
    ∀ (z : Y) (L T : Subgroup Y), Setting z L T →
      (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → memberIndex L T = 3 →
      (∀ Q : Sylow 2 L, ¬ QOddNormalInT z L T Q) →
      TwoSubgroupsFourGenerated (genFittingFStar ↥T) → False

@[expose] def ResidualCFrameLarge : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CIT3Below (Nat.card Y) →
    ∀ (z : Y) (L T : Subgroup Y), Setting z L T →
      (∀ (z' : T) (L' : Subgroup T), ¬ IsClassicalMember3 L' z') → memberIndex L T = 3 →
      (∀ Q : Sylow 2 L, ¬ QOddNormalInT z L T Q) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar ↥T) → False

theorem residualCFrame_of_ranges (hS : ResidualCFrameSmall) (hL : ResidualCFrameLarge) :
    ResidualCFrame := by
  intro Y _ _ hB z L T hset hfree hidx hQ
  by_cases hF : TwoSubgroupsFourGenerated (genFittingFStar ↥T)
  · exact hS Y hB z L T hset hfree hidx hQ hF
  · exact hL Y hB z L T hset hfree hidx hQ hF

end CFSG.ClassicalInvolution.Q3.TA3
