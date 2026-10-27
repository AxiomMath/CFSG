module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedBranch
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PermutableOrderThree

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D2L34BetaMSideO : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    D2L34AllResidue P M →
    GLBStronglyEmbedded 3 M ∧ ∃ U Q : Subgroup G, IsBetaBase H M U ∧ Q ≤ M ∧ Nat.card Q = 3 ∧
      IsS3Parabolic U (U ⊔ Q) ∧ ∀ g : G, ¬ Q.map (MulAut.conj g).toMonoidHom ≤ H

theorem permutableOrderThreeAt : PermutableOrderThreeAt :=
  fun G _ _ M D₀ P₀ Rc hD₀M hD₀n hD₀cop hP₀M hP₀ hNn hRcM hRc hsyl =>
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_permutable_order_three_of_normal
      hD₀M hD₀n hD₀cop hP₀M hP₀ hNn hRcM hRc hsyl

theorem d2L34BetaMSideBase_of_cover
    (hcov : CFSG.AGLEmbeddingD2.Tits.MsidePrelim.D2L34BetaPushUpCover) : D2L34BetaMSideBase :=
  fun d G _ _ P M A H R Rbar K hc hstr hOnly => by
    open CFSG.AGLEmbeddingD2.Tits.MsidePrelim in
    obtain ⟨V, hV, hAV⟩ := D2L34BetaConf.exists_isSylowTwoOf_glbPrimeCore_inf hc
    obtain ⟨C, hCV, hC1, hchar, hcovC⟩ := hcov d G P M A H R Rbar K hc hstr V hV hAV
    have hNV := D2L34BetaConf.normalizer_le_of_char_cover hc hstr hOnly.onlyL34At hV.2.1 hAV hCV
      hC1 hchar hcovC
    exact ⟨V, D2L34BetaConf.isBetaBase_of_isSylowTwoOf hc hV, hAV, hNV,
      D2L34BetaConf.isSylowTwoOf_inf_glbPrimeCore_of_normalizer_le hc hV hAV hNV, hV⟩

theorem d2L34BetaMSideO_of_input
    (hcov : CFSG.AGLEmbeddingD2.Tits.MsidePrelim.D2L34BetaPushUpCover)
    (hin : D2L34BetaMSideInput) (hnc : D2L34BetaMSideNonConstrainedInput) :
    D2L34BetaMSideO := by
  unfold D2L34BetaMSideO
  intro d G _ _ P M A H R Rbar K hc hOnly
  have hstr : GLBStronglyEmbedded 3 M :=
    D2Escape.stronglyEmbedded_of_normalRankFour
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.Konvisser.kFactNormalRankFourThree
      hc.esc hc.glob hc.beta
  exact d2L34BetaMSideX_of_input permutableOrderThreeAt (d2L34BetaMSideBase_of_cover hcov) hin hnc
    d G P M A H R Rbar K hc hOnly
    (CFSG.AGLEmbeddingD2.Tits.MsidePrelim.D2L34BetaConf.d2L34Kmax hc hstr hOnly.onlyL34At)

theorem d2L34BetaMSideO_of_ff
    (hFF : CitedFFL34BestOffender) (hin : D2L34BetaMSideInput)
    (hnc : D2L34BetaMSideNonConstrainedInput) : D2L34BetaMSideO :=
  d2L34BetaMSideO_of_input (CFSG.AGLEmbeddingD2.Tits.MsidePrelim.d2L34BetaPushUpCover hFF) hin hnc

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
