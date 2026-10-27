module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveReeF4
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveSz
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveTits

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


theorem threeFourTwoFiveLie_holds : ThreeFourTwoFiveLie := by
  intro d hd
  rcases hd with hd | hd | hd
  · exact threeFourTwoNoneAt_sz32 hd
  · exact threeFourTwoNoneAt_tits hd
  · exact threeFourTwoNoneAt_reeF4 hd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
