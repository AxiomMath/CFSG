module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBoundsPlus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.SeitzQ2 (SwapPairExclusion)

theorem swapPairExclusion_coordinatePlus_four_of_card (K : Type) [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) :
    SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 4 K)) := by
  obtain ⟨f, -, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  exact swapPairExclusion_coordinatePlus_four ((LinearPilot.four_le_card_iff_two_le hK).1 hq) hK

end CFSG.SeitzReduction.OmegaPilot
