module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618Glue
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop614Core_of_core18 (hS : Setting G) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (h : GL83SmallRankProp614Core18 G) :
    GL83SmallRankProp614Core G := by
  intro P M hsit hsolv he x z hx hz H S hext h0 h1 h2 h3 h4 h5 h6
  exact h P M hsit hsolv he x z hx hz H S hext h0 h1 h2 h3 h4 h5 h6
    (exists_prop614Component hS hKF1 hKF2 hsit hx hz hext h0 h6)

theorem prop614_of_core18 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (h : GL83SmallRankProp614Core18 G) :
    GL83SmallRankProp614 G :=
  prop614_of_core hS hU0 hD2 hK h627 h632 (prop614Core_of_core18 hS hKF1 hKF2 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
