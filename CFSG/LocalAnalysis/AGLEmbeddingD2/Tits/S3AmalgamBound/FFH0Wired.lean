module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFH0Consumer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5PairDerive
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

@[expose] def FFH0Hyp : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ∀ (hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) M))
      (I : Finset (Subgroup (MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) M) hU)))),
      M ≤ Subgroup.normalizer ((conjClosure (quasithinOmegaOneCenter T) M : Subgroup G) : Set G) →
      (∀ L ∈ I, Nat.card L = 6) → autI hU (thompsonJ M) = ⨆ L ∈ I, L →
      IsSylowTwoOf (autI hU (thompsonJ T)) (autI hU (thompsonJ M)) →
      (∀ g ∈ autI hU M, ∀ L ∈ I, B1.conjAut g L ∈ I) → S3Family I →
      ∀ L ∈ I, ∃ H₀ : Subgroup G,
        FFH0Spec M T (conjClosure (quasithinOmegaOneCenter T) M) hU L H₀

theorem ffGroupStep_of_h0 (h0 : FFH0Hyp) : FFGroupStep := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm hfam L hL
  have hF : CharTwo M := hc.glob.charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hVM : conjClosure (quasithinOmegaOneCenter T) M ≤ M :=
    hle.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hBJ := ffBaumStar d G P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm
    hfam
  have ctx : FFCtx M T (conjClosure (quasithinOmegaOneCenter T) M) hU hMN I :=
    ⟨hVM, rfl, hT, hF, hcard, hJM, hSyl, hperm, hfam, hBJ⟩
  obtain ⟨H₀, hspec⟩ := h0 d G P M A H R Rbar K hc hstr hAll T hT hNT hU I hMN hcard hJM hSyl hperm
    hfam L hL
  exact ⟨H₀, hspec.conclusion ctx hL⟩

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
