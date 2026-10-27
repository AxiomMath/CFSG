module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepA
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepB
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepC

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.PartTwo.KFacts

variable {G : Type} [Group G] [Finite G]

theorem prop632_of_prop627 (hKP : KPSz)
    (hK : SmallRankConstraintKFact3) (hS : Setting G) (hU0 : FullCoreLocal G)
    (h627 : GL83SmallRankProp627 G) : GL83SmallRankProp632 G := by
  intro P M hs
  obtain ⟨x, z, g, T, hd⟩ := exists_smallRank3Data hS hU0 h627 hs
  have hO3 := no_normal_index_three_of_situation hS hU0 hs
  have hD := isSolvable_primeCore_of_data hKP hS hs hd hO3
  obtain ⟨e⟩ := nonempty_mulEquiv_wreath_of_data hS hs hd
  have hQ := isSolvable_quotient_of_kfact hK hS hU0 hs hd.point e
  exact ⟨isSolvable_of_primeCore_of_quotient hD hQ, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
