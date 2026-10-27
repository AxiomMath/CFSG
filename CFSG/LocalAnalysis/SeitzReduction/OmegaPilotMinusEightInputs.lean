module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsSwap

public section

namespace CFSG.SeitzReduction.OmegaPilot

section Main

theorem omegaMinusFourInput_of_inputs_six (hswap : OmegaMinusFourSwapRowInput)
    (hcov : OmegaMinusFourCoverInput) (haniso : OmegaMinusFourAnisoCoverInput)
    (hparam : OmegaMinusFourRootParamInput) (huniq : OmegaMinusFourUniqueInput)
    (hend : OmegaMinusFourEndInput) : OmegaMinusFourInput :=
  omegaMinusFourInput_of_inputs_aniso hswap hcov haniso hparam
    (omegaMinusFourRootParamOneTwoInput_of_rootParam hparam) huniq hend

end Main

end CFSG.SeitzReduction.OmegaPilot
