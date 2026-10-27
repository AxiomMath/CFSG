module

public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.A7
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Alt
public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Facts

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem KFactSetting.gl83RelativePairExclusion_of_relPair2 {n : ℕ} (hS : KFactSetting n G)
    (hD1 : TheoremD1 G) (hK : KFactLemma212Ge n) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hT : GL83RelPair2Thompson G) (hA7 : GL83RelPair2A7 G) :
    GL83RelativePairExclusion G := by
  refine gl83RelativePairExclusion_iff.mpr fun p hp P M D R T hd => ?_
  obtain ⟨H, V, hHV⟩ := hS.obstruction.exists_optimal hD1 hp hR h13 hd
  have hfacts := hS.optimalRelPairFacts hD1 hK hp hR h13 hd hHV
  obtain ⟨h3, L, hL, hLA⟩ := hT p hp P M D R T H V hd hHV hfacts
  obtain ⟨hV4, n, hnH, hnD, hjoin, hVT, horb⟩ := hA7 p hp P M D R T H V hd hHV hfacts h3 L hL hLA
  exact hS.obstruction.false_of_card_pCoreOf_lt hD1 hp hR h13 hd hHV hV4
    (hS.obstruction.card_pCoreOf_lt_of_conj hD1 hp hR h13 hd hHV hnH hnD hjoin hVT horb)

theorem relativePairExclusionOfD1Rank4_of_kfacts
    (hK212 : KFactLemma212Ge 4)
    (hK1 : KFactZJFactorizationGe) (hK2 : KFactAlmostSimpleRankTwo) :
    RelativePairExclusionOfD1Rank4 := by
  intro G _ _ _ hnonab hKpr hchar he hpre hD1 hR h13
  have hS : D1Global G := ⟨inferInstance, hnonab, hKpr, hchar, he, hpre⟩
  have hK := KFactSetting.of_d1Global hS
  have hD1' := theoremD1_of_d1For hS.rank hD1
  have hT : GL83RelPair2Thompson G := hK.obstruction.gl83RelPair2Thompson_of_alt hD1' hR h13
    (hK.gl83RelPair2ThompsonAlt_of_kfacts hD1' hR h13 hK1 hK2)
  have hA7 : GL83RelPair2A7 G := gl83RelPair2A7_of_B
    (hK.obstruction.gl83RelPair2A7B_of_module hD1' hR h13 hK.gl83RelPair2A7Module_proved)
  exact hK.gl83RelativePairExclusion_of_relPair2 hD1' hK212 hR h13 hT hA7

end CFSG.LocalAnalysis.RankFourTheoremC
