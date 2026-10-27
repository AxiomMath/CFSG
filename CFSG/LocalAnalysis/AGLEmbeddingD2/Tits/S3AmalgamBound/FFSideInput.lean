module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFCase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.EscapeCover

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.LocalAnalysis.RankThreeTheoremC (D2L34BetaConf3 D2Amb3)
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

@[expose] def FFThompsonInput : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M →
    ¬ thompsonJ T ≤ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) M : Set G)

theorem _root_.CFSG.LocalAnalysis.RankThreeTheoremC.D2L34BetaConf3.not_normalizer_le_of_isSylowTwoOf
    {G : Type} [Group G] [Finite G]
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} [D2Amb3 G]
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ¬ Subgroup.normalizer (T : Set G) ≤ M := by
  intro hNM
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hcov := D2L34BetaConf3.cover_of_isSylowTwoOf hc hstr hT (B := A) (Y := H ⊓ M)
    (le_inf hAH hAM) (IsPGroup.of_card (n := 2) hc.esc.card_A) (by simpa using hc.esc.card_A)
    hT.1 (le_inf hAH hAM) (inf_le_inf_left H hNM)
  have hN : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := hc.normalizer_eq
  have hEq := D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover hc hstr hOnly
    (C := pCoreOf 2 (H ⊓ M))
    (fun k hk => by
      obtain ⟨a, ha, haH, e⟩ := hcov k hk
      exact ⟨a, Subgroup.mem_inf.2 ⟨haH, hN.symm ▸ ha⟩, haH, e⟩)
    hc.esc.maxTwoLocal_M (hN.le.trans inf_le_right)
  exact hc.esc.not_le (hEq ▸ le_rfl)

theorem not_normalizer_le_of_isSylowTwoOf
    {d : TauCeti.ValidLieTypeIndex} {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    ¬ Subgroup.normalizer (T : Set G) ≤ M := by
  have := hc.amb3
  exact hc.toConf3.not_normalizer_le_of_isSylowTwoOf hstr hOnly hT

@[expose] def FFSolvableInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T : Subgroup G), CharTwo M → IsSylowTwoOf T M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ S : Sylow 3 ↥(ffC M T),
      IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
        CFSG.HallHigman.IsPSolvable 3 ↥(ffC M T)

@[expose] def FFRankTwoInput : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M → FFRankTwoCase M T

@[expose] def FFNoncyclicInput : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M → ∀ S : Sylow 3 ↥(ffC M T),
      ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) → False

theorem d2L34BetaMSideInput_of_ff_case
    (hFF : CitedFFL34BestOffender) (hI59 : AGL81I59)
    (hTF : FFThompsonInput) (hSolv : FFSolvableInput)
    (hr2 : FFRankTwoInput) (hnc : FFNoncyclicInput) : D2L34BetaMSideInput := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon
  obtain ⟨T, hTH⟩ := exists_isSylowTwoOf (H ⊓ M)
  have hTM : IsSylowTwoOf T M :=
    (D2L34BetaConf.isSylowTwoOf_of_cover (d2L34BetaPushUpCoverSyl hFF) hc hstr hAll.onlyL34At
      hTH).1
  have hNT' : ¬ Subgroup.normalizer (T : Set G) ≤ M := not_normalizer_le_of_isSylowTwoOf hc hstr hAll.onlyL34At hTH
  have hMtop : M ≠ ⊤ := fun h => hc.esc.not_le (h ▸ le_top)
  have hK : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hc.glob.kProper) M hMtop
  have hF : CharTwo M := hc.glob.charTwo M hc.esc.maxTwoLocal_M.1
  exact exists_normal_order_three_of_ff_case hK hF hcon hI59 hTM
    (hTF d G P M A H R Rbar K hc hstr hAll T hTM hNT')
    (hr2 d G P M A H R Rbar K hc hstr hAll hcon T hTM hNT') (hSolv G M T hF hTM hcon)
    (hnc d G P M A H R Rbar K hc hstr hAll hcon T hTM hNT')

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
