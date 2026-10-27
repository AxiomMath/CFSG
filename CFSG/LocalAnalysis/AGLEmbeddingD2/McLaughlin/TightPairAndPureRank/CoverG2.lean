module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCtx
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeG2

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits


theorem CoverCtx.false_g2_big {W : Type} [Group W] [Finite W] {L S₀ A₁ A₂ : Subgroup W}
    (ctx : CoverCtx L S₀ A₁ A₂) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq4 : 4 ≤ Nat.card K)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* AdjointQuotient .G2 K) : False := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  have h := borelQuotient_g2 e
  exact ctx.false_of_node h (hasSL2Node_g2 (K := K) (⟨0, by decide⟩ : Fin (Tag.rank .G2))).hasOrderThree
    ((rankOneNode_g2 (K := K) (⟨0, by decide⟩ : Fin (Tag.rank .G2))).perfect hq4)

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
