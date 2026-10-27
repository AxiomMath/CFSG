module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeQuot
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeG2
import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.AGLEmbedding.ParabHub CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.RootSystem

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem rankOneNode_g2 (i : Fin (Tag.rank .G2)) :
    RankOneNode (g2Datum K) i (Nat.card K) := by
  obtain ⟨φ, -, hx, hy⟩ := g2_exists_sl2_hom (K := K) i
  exact rankOneNode_of_sl2 (by have := Finite.one_lt_card (α := K); omega)
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := K)
      (RootSystem.ofCartan (g2Datum K).isFiniteType (g2Datum K).divisible)
      (adjDatum_roots (rootOperatorFamily .G2) K))
    (fun c => (hx c).trans (xPar_simple i c).symm)
    (fun c => (hy c).trans (xPar_neg_simple i c).symm) (Or.inl rfl)

theorem parabCore_g2 {Y : Type} [Group Y] [Finite Y] (e : Y ≃* AdjointQuotient .G2 K)
    (hq4 : 4 ≤ Nat.card K) : ParabCore Y (Nat.card K) := by
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  exact (borelQuotient_g2 e).parabCore hq4 (sub_one_dvd_sq_sub_one _) rankOneNode_g2

end G2

end CFSG.AGLEmbedding.ParabPrime
