module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7ResCentV
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7ResCentVLevi

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.SeitzReduction.E7Pilot

variable {K : Type} [Field K] [Finite K] [CharP K 2]


theorem resCent_e7FrameV : Exc.ResCent (e7FramePt K e7FrameV) (e7FrameLine K e7FrameV) :=
  resCent_e7FrameV_of fun _ hy hy2 hyL =>
    mem_parabolicRadical_of_commute_range_spToAdjointE7 hy hy2 hyL

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
