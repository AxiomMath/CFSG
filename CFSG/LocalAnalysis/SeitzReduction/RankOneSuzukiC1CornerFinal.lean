module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Induction
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Corner

public section

namespace CFSG.SeitzReduction.RankOne

section HKS

theorem szC1ExclusionData_holds : SzC1ExclusionData :=
  szC1ExclusionData_of_eightCorner szEightCorner

end HKS

end CFSG.SeitzReduction.RankOne
