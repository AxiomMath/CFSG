module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Ext
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Prime

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem prop614_of_core (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (h : GL83SmallRankProp614Core G) :
    GL83SmallRankProp614 G :=
  prop614_of_ext hS hU0 hD2 h627 h632 (prop614Ext_of_core hS hK h)

end CFSG.LocalAnalysis.RankThreeTheoremC
