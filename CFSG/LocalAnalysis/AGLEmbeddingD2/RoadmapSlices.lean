module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlockSectionParabolic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockSectionInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockSquareInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ONanBlockHeisInner
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MsideAdapter
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveComplete
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding


theorem d2_of_slice_leaves
    (hLowN : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLowN)
    (h93 : Asc81bNineThree)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hΛ : KFactBlockInvertedThree) (hTPLT : CitedBlockTransvectionPLType)
    (hKSP : KFactBlockAltFiveSquareParabolic) (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) (hMS : D2L34BetaMSide)
    (hFP : KFactBlockFiveHeisParabolic)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M := by
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hA7 : CitedBlockAltSevenPL := citedBlockAltSevenPL_holds
  have hFive : KFactBlockFiveNoncyclic := kFactBlockFiveNoncyclic_of_asc81b h93 h86
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  exact d2_of_proved_leaves hLowN h93 hT1 hT2 hT25 hΛ (citedBlockTransvectionPL_of_type hTPLT) hA7
      (kFactBlockAltFiveSectionInner_of_types h86 h93 hFive kFactBlockAltFiveSectionParabolic)
      (kFactBlockAltFiveSquareInner_of_types h86 h93 hTPLT hA7 hKSP) hS3 hJ4
      (d2L34BetaResidueU_of_amalgam d2L34BetaHPara hMS d2L34BetaCoreFree)
      (kFactBlockFiveHeisInner_of_types h86 h93 hTPLT hA7 hFP) hMon7 G hnonab hK hchar he hδ₁ hδ₂
      hD1 p hp P M hM' hPM Q hQ hQrank hQM H hH hQH

theorem d2_of_slice_ff_leaves
    (hLowN : CFSG.LieType.SeitzGeneration.KFactSeitzRankTwoLowN)
    (h93 : Asc81bNineThree)
    (hT1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (hT2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (hT25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hΛ : KFactBlockInvertedThree) (hTPLT : CitedBlockTransvectionPLType)
    (hKSP : KFactBlockAltFiveSquareParabolic) (hS3 : D2PairStrongThree)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11)
    (hFF : CitedFFL34BestOffender)
    (hin : Tits.MsideParabolicEscape.D2L34BetaMSideInput)
    (hnc : Tits.MsideParabolicEscape.D2L34BetaMSideNonConstrainedInput)
    (hFP : KFactBlockFiveHeisParabolic)
    (hMon7 : D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hδ₁ : GLBDeltaOne G) (hδ₂ : GLBDeltaTwo G) (hD1 : D1For G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM' : GLBIsMaxTwoLocal M)
    (hPM : GLBCore p 2 (P : Subgroup G) ≤ M) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hQrank : Open.pRank p Q = 2) (hQM : GLBCore p 1 Q ≤ M) (H : Subgroup G)
    (hH : IsTwoLocal H) (hQH : Q ≤ H) : H ≤ M :=
  d2_of_slice_leaves hLowN h93 hT1 hT2 hT25 hΛ hTPLT hKSP hS3 hJ4
    (Tits.MsideParabolicEscape.d2L34BetaMSide_of_ff hFF hin hnc) hFP hMon7 G hnonab hK hchar he
    hδ₁ hδ₂ hD1 p hp P M hM' hPM Q hQ hQrank hQM H hH hQH

end CFSG.AGLEmbeddingD2
