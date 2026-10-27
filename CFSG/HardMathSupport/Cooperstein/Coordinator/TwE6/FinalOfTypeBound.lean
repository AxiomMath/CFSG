module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Reduction
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjHalf
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6.TwSurv27

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6


theorem coopersteinNoIrrFFTwistedE6_of_typeBound
    (hT : ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2]
      (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)),
      TwTypeBoundStmt hf K hK σ hσ) :
    CoopersteinNoIrrFFTwistedE6 :=
  coopersteinNoIrrFFTwistedE6_of_bounds hT
    (fun _ hf _ _ _ _ hK σ hσ =>
      CFSG.HardMathSupport.Meierfrankenfeld.Proving.TwE6.tw27SurvivorBound_holds hf hK σ hσ)
    (fun _ hf _ _ _ _ hK σ hσ => tw78HalfOffenderBound_holds hf hK σ hσ)
    (fun _ hf _ _ _ _ hK σ hσ => tw78CentreTrivial_holds hf hK σ hσ)

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
