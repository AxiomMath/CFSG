module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapFiSeven
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOverHolds
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockOrderThree
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
public import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34NotOrthogonal

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding


theorem d2_of_beta_leaves (hS : D2SeitzCross)
    (hBHS : CFSG.CGT.PushingUpLit.BHS.BHSLocalCStar) (h93 : Asc81bNineThree)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) (hK2 : KFactParabolicThree)
    (hΛ : KFactBlockInvertedThree)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hTPL : CitedBlockTransvectionPL) (hA7PL : CitedBlockAltSevenPL)
    (hKB : KFactBlockAltFiveSectionInner)
    (hKS : KFactBlockAltFiveSquareInner)
    (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hRes : D2L34BetaResidueU)
    (hF : KFactBlockFiveHeisInner)
    (hC5 : KFactBlockCyclicThreeFive)
    (hB7 : D2IndexCaseAt (.sporadic .B) fun p => p = 7)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_aligned_leaves hS (asc81bEightSix_of_bhs hBHS) h93
      (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs hBHS) hT1 hT2 hT25 hK2 hΛ hKin
      hKP hTPL hA7PL hKB hKS hS3 hJ4
      (d2L34BetaCase_of_residueU kFactL34Outer kFactL34Inner kFactL34NotOrthogonal
          kFactCatalogSchreier kFactL34NormalizerSolvable
          (asc81bEightFour_of_factorization
              (CFSG.CGT.PushingUpLit.Glue.aschbacherLocalFactorization_of_bhs hBHS)) h93
          (d1NoXBlock_of_inputsK hT1 hT2 hT25) hS3 hRes) kFactHSFiveOver_holds hF
      (kFactBlockThreeOrderThree_of_inverted hΛ) hC5 hB7 hMon7 G hnonab hK hchar he hδ₁ hδ₂ hD1 p hp
      P M hM' hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
