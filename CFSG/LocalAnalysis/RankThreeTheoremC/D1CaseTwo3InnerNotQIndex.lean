module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34SqAbs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalPerfectLifts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section GroupTheory

private theorem card_sup_mul_card_inf_of_le_normalizer {X : Type*} [Group X] {E N : Subgroup X}
    (hE : E ≤ Subgroup.normalizer (N : Set X)) :
    Nat.card (N ⊔ E : Subgroup X) * Nat.card (N ⊓ E : Subgroup X) =
      Nat.card N * Nat.card E := by
  have h1 := Subgroup.relIndex_mul_card N (E ⊔ N)
  have h2 := Subgroup.relIndex_mul_card N E
  have h3 : N.relIndex (E ⊔ N) = N.relIndex E := by
    haveI := Subgroup.normal_subgroupOf_of_le_normalizer hE
    haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hE
    exact (Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient E N hE).toEquiv).symm
  rw [inf_eq_left.mpr le_sup_right, h3, sup_comm E N] at h1
  rw [← h1, ← h2, inf_comm N E]
  ring

end GroupTheory

end CFSG.LocalAnalysis.RankThreeTheoremC
