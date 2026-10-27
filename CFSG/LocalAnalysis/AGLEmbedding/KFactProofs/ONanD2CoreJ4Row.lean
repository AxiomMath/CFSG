module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.Open

theorem d2IndexDatum_J4_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .J4) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .J4) := Finite.of_equiv L e.toEquiv
  refine D2IndexDatum.of_mulEquiv Nat.prime_three e
    ⟨?_, Or.inr (Or.inr (Or.inr glbCore_J4_three))⟩
  rw [CFSG.AGLEmbedding.card_outer_J4]
  norm_num

end CFSG.AGLEmbeddingD2
