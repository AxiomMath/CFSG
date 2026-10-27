module

public import CFSG.Open.UniquenessCaseRankThreeMilestoneDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

theorem rankThreeUC_eq_uniqueThreeUC (G : Type) [Group G] [Finite G] :
    CFSG.Open.rankThreeUC G = CFSG.Open.uniqueThreeUC G := rfl

end CFSG.LocalAnalysis.RankThreeUC
