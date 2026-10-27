module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeSporM11
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeSporM12
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeSporJ3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


theorem threeFourSolvThreeSporadic_holds : ThreeFourSolvThreeSporadic := by
  rintro s (rfl | rfl | rfl)
  · exact threeFourSolvThreeNoneAt_m11
  · exact threeFourSolvThreeNoneAt_m12
  · exact threeFourSolvThreeNoneAt_j3

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
