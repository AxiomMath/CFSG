module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaPlusChart

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

section Main

theorem omegaMinusTwoInput_of_ten_cat (h10 : OmegaMinusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) : OmegaMinusTwoInput :=
  omegaMinusTwoInput_of_model h10 hcat omegaMinusTwoEnnolaModelInput_holds

theorem omegaPlusTwoInput_of_ten_cat (h10 : OmegaPlusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) : OmegaPlusTwoInput :=
  omegaPlusTwoInput_of_model h10 hcat omegaPlusTwoEnnolaModelInput_holds

end Main

end CFSG.SeitzReduction.OmegaPilot
