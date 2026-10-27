module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatSporadicFour
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem catSLmSporadicAt_of_four_le {m : ℕ} (hm : 4 ≤ m) : CatSLmSporadicAt m :=
  catSLmSporadicAt_of_monster ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput hm

end CFSG.SeitzReduction.LinearPilot
