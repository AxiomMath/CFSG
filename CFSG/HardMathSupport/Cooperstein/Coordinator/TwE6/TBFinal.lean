module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TB78Dim
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidual

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6


theorem twTypeBoundStmt_proved {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    TwTypeBoundStmt hf K hK σ hσ :=
  twTypeBoundStmt_holds_wide hf K hK σ hσ (twF1Residual_holds hf hK σ hσ) twExistsDigitF2_holds

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
