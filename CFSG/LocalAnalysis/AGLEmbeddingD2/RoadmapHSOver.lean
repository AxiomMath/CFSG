module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapFiveSz
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductions
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding


theorem d2_of_hsOver_leaves (hS : D2SeitzCross)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hK2 : KFactParabolicThree)
    (hΛ : KFactBlockInvertedThree)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hβ : D2L34BetaCase)
    (hHSo : KFactHSFiveOver) (hF : KFactBlockFiveHeisInner) (hII : D2HSFiveCaseTwo)
    (hFi7 : D2IndexCaseAt (.sporadic .Fi24Prime) fun p => p = 7)
    (hB7 : D2IndexCaseAt (.sporadic .B) fun p => p = 7)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_sz_leaves hS (asc81bEightFour_of_factorization hLF) h85 h86 h93 hLF hT1 hT2 hT25 hK2
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hKin hKP
      hC3p hK5p hKB hKS hS3 hJ4 hβ
      (d2HSFiveNonBorel_of hHSo d2HeisLocalEqAt_hs kFactThreeOrFiveDvd kFactCatalogSchreier
          (asc81bEightFour_of_factorization hLF) h85 h86 h93 (d1NoXBlock_of_inputsK hT1 hT2 hT25)
          hK2 (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ)
          hF hII) hFi7 hB7 hMon7 G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM H
      hH hQH

theorem d2_of_hsCase_leaves (hS : D2SeitzCross)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hLF : CFSG.CGT.PushingUpLit.AschbacherLocalFactorization)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hK2 : KFactParabolicThree)
    (hΛ : KFactBlockInvertedThree)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hβ : D2L34BetaCase)
    (hHSo : KFactHSFiveOver) (hF : KFactBlockFiveHeisInner) (hMult : KFactHSMultiplier)
    (hO3 : KFactBlockThreeOrderThree) (hC5 : KFactBlockCyclicThreeFive)
    (hFi7 : D2IndexCaseAt (.sporadic .Fi24Prime) fun p => p = 7)
    (hB7 : D2IndexCaseAt (.sporadic .B) fun p => p = 7)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_hsOver_leaves hS h85 h86 h93 hLF hT1 hT2 hT25 hK2 hΛ hKin hKP hC3p hK5p hKB hKS hS3 hJ4 hβ
    hHSo hF (d2HSFiveCaseTwo_of hHSo d2HeisLocalEqAt_hs kFactThreeOrFiveDvd
      (asc81bEightFour_of_factorization hLF) h85 h86 h93 (d1NoXBlock_of_inputsK hT1 hT2 hT25)
      hK2 (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ)
      hMult hO3 hC5)
    hFi7 hB7 hMon7 G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
