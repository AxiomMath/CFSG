module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Spin
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4OrthProj

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

theorem quasisimpleCentralFourInput_holds :
    QuasisimpleCentralFourInput :=
  quasisimpleCentralFourInput_of_POmegaPlus pOmegaPlusCentralizerInput pOmegaPlusInvolutionInput

theorem quasisimpleTwoPartInput_holds :
    QuasisimpleTwoPartInput :=
  quasisimpleTwoPartInput_of_centralFour quasisimpleCentralFourInput_holds

end CFSG.ComponentClassification.Sol76T13.Hq4
