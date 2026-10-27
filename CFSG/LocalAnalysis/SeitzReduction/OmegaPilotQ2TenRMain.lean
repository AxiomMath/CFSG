module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRFlipModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

theorem omegaMinusTwoTenNormalizedInput_holds : OmegaMinusTwoTenNormalizedInput :=
  omegaMinusTwoTenNormalizedInput_of_flip omegaMinusTwoTenFlipModelInput_holds

end CFSG.SeitzReduction.OmegaPilot
