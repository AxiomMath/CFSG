module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicRowData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BRowsOf

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.AGLEmbedding

section Rows


theorem d2IndexDatum_B_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .B) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .B) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_B_three L ⟨e⟩

end Rows

end CFSG.AGLEmbeddingD2
