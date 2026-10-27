module

public import CFSG.LocalAnalysis.RankFourTheoremC.Dichotomy
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointPrimeFive

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC

theorem theoremCRankFour_of_node_endpoints'
    (hD1 : D1Rank4)
    (hD2 : D2Rank4) (hFC : FullCoreRank4) (hDich : DichotomyRank4) (hE2 : E2NonstrongRank4)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (h313 : GL83NormalElementaryRankFour) (hRB : KFactReeBorelMaximal)
    (hRI : KFactReeInvolution) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h713 : GL83.I_7_13_1) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) : GLBUniqueFour G :=
  theoremCRankFour_of_node_endpoints hD1 hD2 hFC
    (deltaTwoRank4_of_pElement hD1 hFC
      (fun _ _ _ => pElementPrimeFive_holds h243 h244 hsig h313 hRB hRI hInn hWC h713) h313)
    hDich hE2 G hnonab hK hchar he hpre

end CFSG.LocalAnalysis.RankFourTheoremC
