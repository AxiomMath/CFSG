module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatSporadic
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem e7CatalogueClauses_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hX : E7NotOddLieInput) (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput) :
    E7CatalogueClauses :=
  e7CatalogueClauses_of_inputs hGLS hX (catE7Sporadic_of_monster hMinn hMcomp)

variable {K : Type} [Field K]

end CFSG.SeitzReduction.E8Pilot
