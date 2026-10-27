module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAll
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem catOmegaSporadicAt (m : ℕ) : CatOmegaSporadicAt m :=
  catOmegaSporadicAt_of_monster ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput m

end CFSG.SeitzReduction.OmegaPilot
