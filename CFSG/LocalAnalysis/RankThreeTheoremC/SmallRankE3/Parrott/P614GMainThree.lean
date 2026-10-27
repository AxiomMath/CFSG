module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GOutThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

theorem piece619Three_of_chev2OutTwoRank (hOut : CFSG.LieType.ChevTwo.Chev2OutTwoRank) :
    Piece619Three := by
  intro hGen hTI hCGT h135 hKD hTwo hTr G _ _ P M x z H S K hyp st
  have c := P614G.Ctx.of_hyp hyp st
  have hle : pCoreOf 2 H ≤ kRad H S K := le_inf c.core_le le_sup_right
  by_cases hR : pCoreOf 2 H < kRad H S K
  · exact Or.inr (c.lieCase_three hTI hGen hCGT h135 hR)
  · left
    have hR0 : kRad H S K = pCoreOf 2 H := (eq_of_le_of_not_lt hle hR).symm
    by_cases hcyc : IsCyclic c.rhoS
    · obtain ⟨a, haS, haO, hidx⟩ := c.exists_transvection hcyc
      obtain ⟨ε⟩ := c.nonempty_equiv_alt5 hR0 hTr haS haO hidx
      exact c.a5Case hR0 ε haS haO
    · exact (c.false_of_not_cyclic_three hR0 hKD hTwo hOut hcyc).elim

section Certs


theorem piece619Three_holds : Piece619Three :=
  piece619Three_of_chev2OutTwoRank P614G.chev2OutTwoRank_holds

end Certs

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
