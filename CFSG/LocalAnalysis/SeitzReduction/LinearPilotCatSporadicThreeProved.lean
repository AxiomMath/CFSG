module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicThree
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem catSLmSporadicAt_three_of_outer (hSuz : SuzOuterL34Input) (hON : ONOuterL34Input) :
    CatSLmSporadicAt 3 :=
  catSLmSporadicAt_three_of_inputs ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput hSuz hON

end CFSG.SeitzReduction.LinearPilot
