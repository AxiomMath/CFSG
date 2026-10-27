module

public import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG

theorem isCyclic_of_pRank_le_one {G : Type} [Group G] [Finite G] {p : Nat} (hp : p.Prime)
    (hod : p ≠ 2) (hG : IsPGroup p G) (h : CFSG.Open.pRank p (⊤ : Subgroup G) ≤ 1) :
    IsCyclic G := by
  refine CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one hp hod hG ?_
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top]

end CFSG

end
