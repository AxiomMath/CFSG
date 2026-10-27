module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TwoImageLowRank
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageCensus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem oneImageLowRankResidue_of_clauseO (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hΛ : KFactBlockInvertedThree) (hU : OutU33) (hL5 : OutL5) (hO27 : OutL27)
    (hK1 : KFactLowRankNineThreeTwo) (hK2 : KFactOrthogonalTwoLieRank) :
    OneImageLowRankResidue := by
  intro G _ _ P M A H R hctx _ L hL hk1 hlow hZ
  have hpr := hctx.pair
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h84 : Asc81bEightFour := asc81bEightFour_of_factorization hfact
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have h86 : Asc81bEightSix :=
    asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hH := hctx.esc.pRank_H
  have hM4 := hctx.esc.four_le_pRank_M hctx.beta
  have hthree : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L := fun L hL =>
    hpr.blockHasThree h85 h86 h93 hX kFactParabolicThree
      (citedBlockThreeTransvection_of_inverted hΛ) (kFactBlockThreeAltSeven_of_inverted hΛ) hL
  have ho := clauseO_of_pair_rank_le_two hLF h418 hL27 h93 hD2 hU hL5 hO27 hK1 hK2 hctx hL
    (by omega) hZ
  have hrq := pRank_top_quot_center_eq hL.le hZ
  have hrank : ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsElemAbelian 3 E →
      Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2 := by
    intro E hEN hEA
    refine pRank_le_pRank_inf_centralizer_add_of_cover Nat.prime_three hEN
      (fun x hx => ho x (hEN hx) (isPGroup_zpowers_of_pow_eq_one (hEA.2 x hx))) ?_
    omega
  exact hpr.false_of_one_weakSBlock_of_autRank h84 h86 hX hH hM4 hthree hL hk1 hrank
    (exists_order_three_noncentral hL.le (hthree L hL) hZ)

end CFSG.AGLEmbeddingD2.McLaughlin
