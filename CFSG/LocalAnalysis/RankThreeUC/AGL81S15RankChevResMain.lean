module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevResStmt
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevRes
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevLinEasy
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUniEasy

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem lieOddRankChev_of_res (hG : CFSG.Open.GriessAllModelsStatement)
    (hRes : LieOddRankChevRes) : LieOddRankChev :=
  lieOddRankChev_of_parts hG (lieOddRankChevLinEasy_holds hG) (lieOddRankChevUniEasy_holds hG) hRes

end CFSG.LocalAnalysis.RankThreeUC.S15
