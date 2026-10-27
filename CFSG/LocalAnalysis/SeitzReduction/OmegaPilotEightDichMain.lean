module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBoundsMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightDich

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

theorem omegaPlusFourSwapInput_of_swapComm (hcomm : PlusFourSwapCommInput) :
    OmegaPlusFourSwapInput :=
  omegaPlusFourSwapInput_of_comm hcomm swapPairExclusion_coordinatePlus_four_of_card

end CFSG.SeitzReduction.OmegaPilot
