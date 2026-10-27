module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineRankTorus
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCount

public section

namespace CFSG.SeitzReduction.RankOne

section Certificates

theorem u3SixNineFourInput_holds : U3SixNineFourInput :=
  u3SixNineFourInput_of_rankCountInput rankCountInput_holds

end Certificates

end CFSG.SeitzReduction.RankOne
