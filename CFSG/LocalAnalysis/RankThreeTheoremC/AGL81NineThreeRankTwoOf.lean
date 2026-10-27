module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem kFactNineThreeRankTwo_of_listRankOne (h : KFactNineThreeListRankOne) :
    KFactNineThreeRankTwo :=
  fun p Y _ _ K _ hK h1 => h p Y K (Or.inl hK) h1

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
