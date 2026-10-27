module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreFi24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.Sporadic.Schreier.Fi24Schreier

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.Open

theorem d2IndexDatum_Fi24Prime_seven :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Fi24Prime) →
      D2IndexDatum L 7 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Fi24Prime) := Finite.of_equiv L e.toEquiv
  refine D2IndexDatum.of_mulEquiv Nat.prime_seven e
    ⟨?_, Or.inr (Or.inr (Or.inr glbCore_Fi24Prime_seven))⟩
  have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (NativeSporadic.Carrier .Fi24Prime)) = 2 :=
    CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime
  rw [h2]
  norm_num

end CFSG.AGLEmbeddingD2
