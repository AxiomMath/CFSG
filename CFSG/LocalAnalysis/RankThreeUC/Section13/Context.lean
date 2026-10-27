module


public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section13

variable {G : Type} [Group G] [Finite G]

abbrev Bar (M : Subgroup G) : Type := ↥M ⧸ CFSG.pCore 2 ↥M

end Section13

end CFSG.LocalAnalysis.RankThreeUC
