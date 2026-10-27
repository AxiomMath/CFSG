module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.FusionDefs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FixedTwoComponentLocation : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (β : MulAut X), (∀ x, β (β x) = x) →
    ∀ T : Subgroup X, T ≤ fixedSubgroup β → IsPComponent 2 (T.subgroupOf (fixedSubgroup β)) →
    ∃ X₁ : Subgroup X, IsPComponent 2 X₁ ∧
      ((X₁.map β.toMonoidHom = X₁ ∧ T ≤ X₁) ∨
        (X₁.map β.toMonoidHom ≠ X₁ ∧
          Nonempty (↥T ⧸ Open.fusionZStar ↥T ≃* ↥X₁ ⧸ Open.fusionZStar ↥X₁) ∧
          Nat.card (↥T ⧸ pPrimeCore 2 ↥T) ∣ Nat.card (↥X₁ ⧸ pPrimeCore 2 ↥X₁)))

end CFSG.ComponentClassification.GS82PumpInputs
