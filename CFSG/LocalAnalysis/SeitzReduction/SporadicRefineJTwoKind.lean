module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwoSylow
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWBFinal

public section

namespace CFSG.SeitzReduction.SporadicRefine

theorem linearTwoSmallKindAtInput_five_of_sylow
    (hrk : LinearPilot.LFiveSmallKindRankInput) (hJ : J2SylowSupportInput) :
    LinearPilot.LinearTwoSmallKindAtInput 5 :=
  LinearPilot.linearTwoSmallKindAtInput_five_of LinearPilot.lFiveWOneInput hrk
    (lFiveJTwoInput_of_sylow hJ)

end CFSG.SeitzReduction.SporadicRefine
