module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapNodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

theorem omegaPlusSwapRowInput_of_swapPairExclusion
    (hP : ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → 6 ≤ n →
      SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus n K))) :
    OmegaPlusSwapRowInput := by
  intro G _ _ L hset n f K _ _ _ hKc hq hn e t ht hKt hN hrow
  exact false_of_swapRow_omega_plus_of_swapPairExclusion hset hKc hq (by omega) e ht hKt hN hrow
    (hP n K hq hn)

end CFSG.SeitzReduction.OmegaPilot
