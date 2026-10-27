module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwMain
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwHSBridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.OddStandard.AltStdSec.SwapPartner


theorem ys04b_holds : SwapFrameP2Two :=
  swapFrameP2Two_of_inputs twHSFusion_holds

end CFSG.OddStandard.AltStdSec.SwapPartner
