module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOdd
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTrialityThreeChars

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.HardMathSupport.Lang.Coordinator

theorem outerFixedOrder_odd_aux
    (h1 : EllQ1Bound) (h2 : MinusToralBound) (h3 : MinusEllBound) :
    OuterFixedOrderTrialityThreeChar (5 ≤ ·) := by
  intro K _ _ n ℓ f hℓ hadm hmodel α hα3 hαin
  refine Or.inr ?_
  rcases hmodel with ⟨ht, -⟩ | ⟨-, -, hM⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact outerFixedOrder_trialityD4_three_odd_aux h1 h2 h3 hadm.1 hℓ hadm.2.1 K hM.2 α hα3 hαin
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.HardMathSupport.Lang.E6Descent
