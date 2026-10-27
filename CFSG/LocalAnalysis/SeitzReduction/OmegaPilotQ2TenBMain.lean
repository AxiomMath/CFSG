module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBField
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesXCharCat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)

theorem omegaEightSporadicStatement_proved : OmegaEightSporadicStatement :=
  omegaEightSporadicStatement_holds monsterInnerInput monsterLocalComponentsInput

theorem omegaCatalogueClausesAt_four_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    OmegaCatalogueClausesAt 4 :=
  omegaCatalogueClausesAt_four_of_xchar hGLS monsterInnerInput monsterLocalComponentsInput

theorem omegaMinusTwoTenInput_of_gls3_fieldLie (hGLS : GLS3OddLieAutComponentsInput)
    (hlie : OmegaMinusTwoTenFieldLieInput) : OmegaMinusTwoTenInput :=
  omegaMinusTwoTenInput_of_lie (omegaCatalogueClausesAt_four_of_gls3 hGLS)
    omegaEightSporadicStatement_proved hlie

theorem omegaPlusTwoTenInput_of_gls3_fieldLie (hGLS : GLS3OddLieAutComponentsInput)
    (hlie : OmegaPlusTwoTenFieldLieInput) : OmegaPlusTwoTenInput :=
  omegaPlusTwoTenInput_of_lie (omegaCatalogueClausesAt_four_of_gls3 hGLS)
    omegaEightSporadicStatement_proved hlie

end CFSG.SeitzReduction.OmegaPilot
