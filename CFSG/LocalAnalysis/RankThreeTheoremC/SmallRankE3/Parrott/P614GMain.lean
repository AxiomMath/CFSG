module

public import CFSG.LieType.ChevTwo.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Group
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Single

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

section Certs

theorem P614G.chev2OutTwoRank_holds : CFSG.LieType.ChevTwo.Chev2OutTwoRank :=
  CFSG.LieType.ChevTwo.chev2OutTwoRank_of_leaves fun _ _ _ h =>
    CFSG.HardMathSupport.Cooperstein.StructureLie.outTwoRank_of_isClassicalTwoOrG2 h

end Certs

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
