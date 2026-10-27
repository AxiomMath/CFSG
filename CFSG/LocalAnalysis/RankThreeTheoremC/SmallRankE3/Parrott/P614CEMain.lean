module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614CECoreTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614CEOmega

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

theorem pieceCoreTwo_holds : PieceCoreTwo :=
  fun hK1 hK2 hK G _ _ => P614CE.coreTwo_of_kfacts hK1 hK2 hK G

theorem pieceOmega_holds : PieceOmega :=
  fun h64 G _ _ => P614CE.omegaFalse_of_kfact64iii h64 G

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
