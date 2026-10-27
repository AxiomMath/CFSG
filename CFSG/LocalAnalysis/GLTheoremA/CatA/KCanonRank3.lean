module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Rank3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InnRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open


theorem rank3_of_inn (hInn : Rk2InnRankOn rk2SmallTag) (G : Type) [Group G] [Finite G] :
    RankThreeLabelAt G :=
  rankThreeLabelAt_of_tables hInn G

theorem rank3_holds (G : Type) [Group G] [Finite G] : RankThreeLabelAt G :=
  rank3_of_inn (fun lab hl _ => rk2InnRank_of_kRank rk2KRank lab hl trivial) G

end CFSG.LocalAnalysis.GLTheoremA
