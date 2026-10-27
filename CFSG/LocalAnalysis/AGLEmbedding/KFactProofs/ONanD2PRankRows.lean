module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicRowData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankHNFive

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint

section Rows


theorem d2IndexDatum_Suz_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Suz) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Suz) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Suz_three L ⟨e⟩

theorem d2IndexDatum_ONan_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .ONan) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .ONan) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_ONan_three L ⟨e⟩

theorem d2IndexDatum_Fi22_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Fi22) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Fi22) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Fi22_three L ⟨e⟩

theorem d2IndexDatum_HN_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .HN) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .HN) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_HN_three L ⟨e⟩

theorem d2IndexDatum_Ly_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Ly) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Ly) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Ly_three L ⟨e⟩

theorem d2IndexDatum_Th_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Th) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Th) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Th_three L ⟨e⟩

theorem d2IndexDatum_Fi23_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Fi23) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Fi23) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Fi23_three L ⟨e⟩

theorem d2IndexDatum_Co1_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Co1) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Co1) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Co1_three L ⟨e⟩

theorem d2IndexDatum_Fi24Prime_three :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Fi24Prime) →
      D2IndexDatum L 3 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Fi24Prime) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_three (by norm_num)
    three_le_pRank_Fi24Prime_three L ⟨e⟩

theorem d2IndexDatum_Co1_five :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Co1) →
      D2IndexDatum L 5 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Co1) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_five (by norm_num)
    three_le_pRank_Co1_five L ⟨e⟩

theorem d2IndexDatum_Ly_five :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .Ly) →
      D2IndexDatum L 5 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Ly) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_five (by norm_num)
    three_le_pRank_Ly_five L ⟨e⟩

theorem d2IndexDatum_HN_five :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier .HN) →
      D2IndexDatum L 5 := by
  intro L _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .HN) := Finite.of_equiv L e.toEquiv
  exact d2IndexDatum_carrier_of_pRank (by decide) Nat.prime_five (by norm_num)
    three_le_pRank_HN_five L ⟨e⟩

end Rows

end CFSG.AGLEmbeddingD2
