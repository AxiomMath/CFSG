module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeLieL28
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeLieG28
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeLieSp48
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeLieL34
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeLieTits

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


theorem threeFourSolvThreeLie_holds : ThreeFourSolvThreeLie := by
  rintro d (⟨q, hq2, ⟨hq3, hd | hd | hd⟩ | ⟨hq2', hd⟩⟩ | hd)
  · exact threeFourSolvThreeNoneAt_l28 q d hq2 hq3 hd
  · exact threeFourSolvThreeNoneAt_g28 q d hq2 hq3 hd
  · exact threeFourSolvThreeNoneAt_sp48 q d hq2 hq3 hd
  · exact threeFourSolvThreeNoneAt_l34 q d hq2 hq2' hd
  · exact threeFourSolvThreeNoneAt_tits d hd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
