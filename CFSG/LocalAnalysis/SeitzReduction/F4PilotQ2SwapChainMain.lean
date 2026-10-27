module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainConfig
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapExcl

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

theorem twoSwapChainInput_holds : TwoSwapChainInput :=
  twoSwapChainInput_of_model twoChainModelInput_holds

theorem twoSwapPairInput_holds : TwoSwapPairInput :=
  twoSwapPairInput_of_chainInput' twoSwapChainInput_holds

end CFSG.SeitzReduction.F4Pilot
