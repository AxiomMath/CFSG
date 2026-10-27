module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapBeta
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInner
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2DatumB7
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzLowCross
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCyclicFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycG2

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

theorem d2IndexCaseAt_B_seven :
    D2IndexCaseAt (.sporadic .B) fun p => p = 7 := by
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group .B
  refine d2IndexCaseAt_of_datum fun L _ _ ⟨e⟩ p hp => ?_
  subst hp
  exact d2IndexDatum_B_seven (e.trans f.symm)

theorem d2_of_proved_leaves
    (hLowN : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLowN)
    (h93 : Asc81bNineThree)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hΛ : KFactBlockInvertedThree)
    (hTPL : CitedBlockTransvectionPL) (hA7PL : CitedBlockAltSevenPL)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner) (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hRes : D2L34BetaResidueU)
    (hF : KFactBlockFiveHeisInner)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_beta_leaves (d2SeitzCross_of_lowN hLowN)
    CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved h93 hT1 hT2
    hT25 kFactParabolicThree hΛ TwoGenInner.kFactTwoGenInner kFactParabolicPrime hTPL hA7PL hKB
    hKS hS3 hJ4 hRes hF (kFactBlockCyclicThreeFive_of_lie h93
        (BlockCyc.lieCyclicParabolic_of BlockCyc.lieCyclicG2) BlockCyc.lieCyclicOrthogonal)
    d2IndexCaseAt_B_seven hMon7 G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM
    H hH hQH

end CFSG.AGLEmbeddingD2
