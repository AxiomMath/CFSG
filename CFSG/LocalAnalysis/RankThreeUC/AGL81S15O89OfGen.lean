module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15

theorem o89_of_gen (h : O89Gen) : O89 := by
  intro G _ _ hS hUC M hM hwit hstrong H hH
  have hH3 : CFSG.Open.pRank 3 H ≤ 3 :=
    (CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) H hH).trans (le_of_eq hS.rank)
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (RankThree.cStarGen_of_rankThreeUC hS hUC) M hM ⟨p, hp⟩ hstrong H hH hH3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
