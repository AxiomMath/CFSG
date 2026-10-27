module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3RankTwo
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFH0Consumer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.FFH0Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem ffGroupStep3 : FFGroupStep3 G := by
  intro d P M A H R Rbar K ctx hstr hcon T hT hNT hU I hMN hcard hJM hSyl hperm hfam L hL
  have := ctx.amb
  have hc := ctx.conf
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hVM : conjClosure (quasithinOmegaOneCenter T) M ≤ M :=
    hle.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hVT : conjClosure (quasithinOmegaOneCenter T) M ≤ T :=
    hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
  have hBJ : autI hU (baum T) ≤ autI hU (thompsonJ M) :=
    autI_baum_le_autI_thompsonJ hMN hT hVT hfam hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
      hperm
  have hctx : FFCtx M T (conjClosure (quasithinOmegaOneCenter T) M) hU hMN I :=
    ⟨hVM, rfl, hT, hF, hcard, hJM, hSyl, hperm, hfam, hBJ⟩
  obtain ⟨H₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    FFH0Hyp.exists_H₀ invariantCyclicSupplement ⟨hF, hT, hle, hfam, hcard, hJM, hSyl, hperm, hL⟩
      hMN
  exact ⟨H₀, FFH0Spec.conclusion hctx hL
    (⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :
      FFH0Spec M T (conjClosure (quasithinOmegaOneCenter T) M) hU L H₀)⟩

theorem ffRankTwoInput3_proved
    (hX : D1NoXBlock3 G) : FFRankTwoInput3 G :=
  ffRankTwoInput3_of_nodes hX ffGroupStep3

theorem ffNoncyclicInput3_proved
    (hI59 : AGL81I59) (hX : D1NoXBlock3 G) : FFNoncyclicInput3 G :=
  ffNoncyclicInput3_of_nodes hI59 hX ffGroupStep3

end CFSG.LocalAnalysis.RankThreeTheoremC
