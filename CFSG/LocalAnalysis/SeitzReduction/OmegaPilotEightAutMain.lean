module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightAutMinusUnique
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightBounds

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

theorem omegaPlusFourLinearTwoPartInput_holds : OmegaPlusFourLinearTwoPartInput :=
  fun _ _ _ _ _ hg _ => omegaLinearInvolutionTwoPart_coordinatePlus_four hg

theorem omegaMinusFourUniqueInput_holds : OmegaMinusFourUniqueInput :=
  omegaMinusFourUniqueInput_of_linear omegaPlusFourLinearTwoPartInput_holds

end CFSG.SeitzReduction.OmegaPilot
