module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapUnique

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

theorem seitzExclusion_highE8_of_inputs''' (hGLS : GLS3OddLieAutComponentsInput)
    (hE7Odd : E7NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (h2 : E8TwoInput) :
    SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_inputs'' hGLS hE7Odd hMinn hMcomp e8SwapRowCTInput_holds
    e8SwapRowUniqueInput_holds h2

end CFSG.SeitzReduction.E8Pilot
