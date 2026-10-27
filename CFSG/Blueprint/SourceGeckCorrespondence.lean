module

public import CFSG.Blueprint.SourceExceptionalRootData
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Blueprint.Chevalley Module

theorem nonempty_ringEquiv_of_card_eq (K₁ K₂ : Type) [Field K₁] [Field K₂] [Finite K₁]
    [Finite K₂] (hcard : Nat.card K₁ = Nat.card K₂) : Nonempty (K₁ ≃+* K₂) := by
  have := Fintype.ofFinite K₁
  have := Fintype.ofFinite K₂
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  exact ⟨FiniteField.ringEquivOfCardEq hcard⟩

end CFSG.Blueprint.EvenSource
