module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockCensus
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem pairBlockCensus (hLF : LargeFieldParabolic) (h418 : Agl418) (hL27 : L2SevenRankOne)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G)
    (hctx : PairStrongCtx P M A H R) (L : Subgroup G)
    (hw : IsWeakSBlock M (pCoreOf 2 H) L) : BlockCensus M (pCoreOf 2 H) L := by
  have hfact := CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
  have h85 : Asc81bEightFive := asc81bEightFive_of_factorization hfact
  have hX : NoXBlockFor G := hD2.noXBlockFor hctx.glob.toD1Global
  have hnot := hctx.pair.nineThree_not_one h85 hX hw
  exact blockCensus hLF h418 hL27 hw (hctx.pair.nineThree h93 hw) hnot.1 hnot.2
    (d2PairSolv G hctx.glob hctx.d1 P M A H R hctx.esc hctx.max hctx.beta hctx.pair
      hctx.strong hctx.perf L hw)

end CFSG.AGLEmbeddingD2.McLaughlin
