module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Base
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerPermutable
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerCentralized
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoLayerCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def D2L34BetaLayerExists3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∃ L : Subgroup G, IsRankTwoLayer M L

@[expose] def D2L34BetaLayerCentralized3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ L : Subgroup G, IsRankTwoLayer M L →
      ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M

@[expose] def D2L34BetaLayerSylow3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ U : Subgroup G, IsBetaBase H M U → IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) →
      A ≤ Subgroup.normalizer (U : Set G) → Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      ∀ L : Subgroup G, IsRankTwoLayer M L →
        IsSylowTwoOf (starImg M U ⊓ starImg M L) (starImg M L)

@[expose] def D2L34BetaLayerAutImage3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ L : Subgroup G, ∀ hlay : IsRankTwoLayer M L,
      haveI : (starImg M L).Normal := normal_starImg hlay.2.2.1
      AutImageOK (starImg M L)

@[expose] def D2L34BetaLayerPermutable3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ U : Subgroup G, IsBetaBase H M U → IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) →
      A ≤ Subgroup.normalizer (U : Set G) → Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      ∀ L : Subgroup G, IsRankTwoLayer M L →
        ∃ P₁ : Subgroup G, P₁ ≤ L ∧ Nat.card P₁ = 3 ∧ (P₁ : Set G) * U = U * P₁

variable {G : Type} [Group G] [Finite G]

theorem nonConstrainedInput3_of_structure (hL : D2L34BetaLayerExists3 G)
    (hC : D2L34BetaLayerCentralized3 G) (hP : D2L34BetaLayerPermutable3 G) :
    D2L34BetaMSideNonConstrainedInput3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax hcon U hU hUQ hAU hNHU hsylU
  obtain ⟨L, hlay⟩ := hL d P M A H R Rbar K ctx hstr hKmax hcon
  obtain ⟨P₁, hP₁L, hP₁c, hperm⟩ :=
    hP d P M A H R Rbar K ctx hstr hKmax hcon U hU hUQ hAU hNHU hsylU L hlay
  exact ⟨P₁, L, hlay.1, hlay.2.2.1, hP₁L, hP₁c, hperm,
    hC d P M A H R Rbar K ctx hstr hKmax hcon L hlay,
    simpleNonabelianModulo_of_isRankTwoLayer hlay⟩

theorem d2L34BetaLayerPermutable3_of (hK : KFactRankTwoSylowPermute)
    (hSyl : D2L34BetaLayerSylow3 G) (hAut : D2L34BetaLayerAutImage3 G) :
    D2L34BetaLayerPermutable3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax hcon U hU hUQ hAU hNHU hsylU L hlay
  exact exists_permuting_of_rankTwoLayer hK hU.1
    ((hUQ.1.trans (glbPrimeCore_le 3 _)).trans inf_le_right) hsylU hlay
    (hSyl d P M A H R Rbar K ctx hstr hKmax hcon U hU hUQ hAU hNHU hsylU L hlay)
    (hAut d P M A H R Rbar K ctx hstr hKmax hcon L hlay)

theorem d2L34BetaLayerCentralized3_of
    (hFF : CitedFFL34BestOffender) (hK : KFactRankTwoE9) :
    D2L34BetaLayerCentralized3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax hcon L hlay a ha l hl
  have := ctx.amb
  exact D2L34BetaConf3.commutator_mem_of_rankTwoLayer hK ctx.conf hstr
    (fun _ hTH => (D2L34BetaConf3.isSylowTwoOf_of_cover hFF ctx.conf hstr
      ctx.allResidue.onlyL34At hTH).1) hlay ha hl

theorem d2L34BetaMSideNonConstrainedInput3_of_layer
    (hFF : CitedFFL34BestOffender) (hE9 : KFactRankTwoE9)
    (hK : KFactRankTwoSylowPermute) (hL : D2L34BetaLayerExists3 G)
    (hSyl : D2L34BetaLayerSylow3 G) (hAut : D2L34BetaLayerAutImage3 G) :
    D2L34BetaMSideNonConstrainedInput3 G :=
  nonConstrainedInput3_of_structure hL (d2L34BetaLayerCentralized3_of hFF hE9)
    (d2L34BetaLayerPermutable3_of hK hSyl hAut)

end CFSG.LocalAnalysis.RankThreeTheoremC
