module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBGlobalMinus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBGlobal

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)

theorem omegaMinusTwoTenInput_of_gls3_global (hGLS : GLS3OddLieAutComponentsInput)
    (hglob : OmegaMinusTwoTenFieldGlobalInput) : OmegaMinusTwoTenInput :=
  omegaMinusTwoTenInput_of_gls3_fieldLie hGLS (omegaMinusTwoTenFieldLieInput_of_global hglob)

theorem omegaPlusTwoTenInput_of_gls3_global (hGLS : GLS3OddLieAutComponentsInput)
    (hglob : OmegaPlusTwoTenFieldGlobalInput) : OmegaPlusTwoTenInput :=
  omegaPlusTwoTenInput_of_gls3_fieldLie hGLS (omegaPlusTwoTenFieldLieInput_of_global hglob)

theorem omegaCatalogueClausesAt_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) (m : ℕ) :
    OmegaCatalogueClausesAt m :=
  omegaCatalogueClausesAt_of_xchar hGLS
    (catOmegaSporadicAt_of_monster monsterInnerInput monsterLocalComponentsInput m)

end CFSG.SeitzReduction.OmegaPilot
