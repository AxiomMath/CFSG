module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreTh
public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.Open

theorem d2IndexDatum_Th_five :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Th) →
      D2IndexDatum L 5 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Th) := Finite.of_equiv L e.toEquiv
  refine D2IndexDatum.of_mulEquiv Nat.prime_five e
    ⟨?_, Or.inr (Or.inr (Or.inr glbCore_Th_five))⟩
  rw [CFSG.RankThree.PartOne.SPOR.card_outer_Th]
  norm_num

end CFSG.AGLEmbeddingD2
