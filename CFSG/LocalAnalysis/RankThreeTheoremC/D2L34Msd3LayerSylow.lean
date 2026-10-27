module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Layer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.Tits CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def D2L34BetaInvariantTwoInCore3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ∀ X : Subgroup G, X ≤ H ⊓ M → IsPGroup 2 X → A ≤ Subgroup.normalizer (X : Set G) →
      X ≤ GLBPrimeCore 3 (H ⊓ M)

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaLayerSylow3_of (hinvH : D2L34BetaInvariantTwoInCore3 G)
    (hCent : D2L34BetaLayerCentralized3 G) (hS : InvariantSylowStmt) :
    D2L34BetaLayerSylow3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax hcon U hU hUQ hAU hNHU hsylU L hlay
  exact isSylowTwoOf_starImg_inf_of_escape hS ctx.conf.esc
    (hinvH d P M A H R Rbar K ctx hstr hKmax) hU hAU hNHU hUQ hlay
    (hCent d P M A H R Rbar K ctx hstr hKmax hcon L hlay)

end CFSG.LocalAnalysis.RankThreeTheoremC
