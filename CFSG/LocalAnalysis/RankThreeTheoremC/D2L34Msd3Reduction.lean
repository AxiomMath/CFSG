module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Escape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFSolvable
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PermutableOrderThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Base

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.Tits CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_order_three_of_ctx3
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hr2 : FFRankTwoInput3 G) (hnc : FFNoncyclicInput3 G)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (h : D2L34SideCtx3 G d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) :
    ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
      ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal := by
  have := h.amb
  have hc := h.conf
  have hOnly := h.allResidue.onlyL34At
  obtain ⟨T, hTH⟩ := exists_isSylowTwoOf (H ⊓ M)
  have hTM : IsSylowTwoOf T M :=
    (D2L34BetaConf3.isSylowTwoOf_of_cover hFF hc hstr hOnly hTH).1
  have hNT' : ¬ Subgroup.normalizer (T : Set G) ≤ M :=
    D2L34BetaConf3.not_normalizer_le_of_isSylowTwoOf hc hstr hOnly hTH
  have hMtop : M ≠ ⊤ := fun hh => hc.esc.not_le (hh ▸ le_top)
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1
        (D2Amb3.glob (G := G)).kProper) M hMtop
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal h.setting h.sigma h.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M :=
    hP3.ge.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hPM)
  exact exists_normal_order_three_of_ff_case3 hK hF hcon hI59 hTM
    (fun hJ hC3 => D2L34BetaConf3.false_of_thompsonJ_le_of_coprime hc hstr h3 hTM hNT' hJ hC3)
    (hr2 d P M A H R Rbar K h hstr hcon T hTM hNT') (ffSolvableInput G M T hF hTM hcon)
    (hnc d P M A H R Rbar K h hstr hcon T hTM hNT')

section Permuted

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem d2L34BetaMSidePermuted3_of_orderThree (hc : D2L34BetaConf3 d P M A H R Rbar K)
    (hstr : GLBStronglyEmbedded 3 M) {P₀ : Subgroup G} (hP₀M : P₀ ≤ M) (hP₀ : Nat.card P₀ = 3)
    (hNn : ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal) {U : Subgroup G}
    (hU : IsBetaBase H M U) (hNHU : Subgroup.normalizer (U : Set G) ≤ H)
    (hsylU : IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M)) : PermutedConcl H M :=
  D2L34BetaConf3.permutedConcl_of_orderThree
    (fun _ _ _ _ _ _ _ hD₀M hD₀n hD₀cop hP₀M hP₀ hNn hRcM hRc hsyl =>
      CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_permutable_order_three_of_normal
        hD₀M hD₀n hD₀cop hP₀M hP₀ hNn hRcM hRc hsyl)
    hc hstr hP₀M hP₀ hNn hU hNHU hsylU

end Permuted

end CFSG.LocalAnalysis.RankThreeTheoremC
