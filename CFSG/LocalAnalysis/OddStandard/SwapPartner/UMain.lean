module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UMainCore
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayHolds
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.InputLHolds

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

theorem ys04a_holds
 : SwapFrameP2One :=
  ys04a_of_inputs dihedralOuterInvolutionFact_holds nonExactShapeEightLookup_holds hsFacts_holds

end CFSG.OddStandard.AltStdSec.SwapPartner
