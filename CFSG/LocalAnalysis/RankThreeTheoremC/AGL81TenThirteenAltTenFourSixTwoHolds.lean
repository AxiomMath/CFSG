module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenFourSixTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding

theorem kFactFourSixTwo_holds
    (hGA : GriessAllModelsStatement) : KFactFourSixTwo :=
  kFactFourSixTwo_of (kFactCompParabTwoFives_of_griess hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
