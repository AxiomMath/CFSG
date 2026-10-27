module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoGTwoEight
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSpFourEight
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoPairSpSix
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTits

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


theorem threeFourTwoThreePairs_holds : ThreeFourTwoThreePairs := by
  rintro d (⟨q, hq2, ⟨hq3, hd | hd⟩ | ⟨hq1, hd⟩⟩ | hd)
  · exact threeFourTwoAt_g28 q d hq2 hq3 hd
  · exact threeFourTwoAt_sp48 q d hq2 hq3 hd
  · exact threeFourTwoAt_spSixTwo hq2 hq1 hd
  · exact threeFourTwoAt_tits3 d hd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
