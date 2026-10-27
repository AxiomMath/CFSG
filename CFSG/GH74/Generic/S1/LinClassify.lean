module

public import CFSG.GH74.Generic.S1.LinForm
public import CFSG.GH74.Generic.S1.LinDiag

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank

theorem classify_lin {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (α : MulAut ↥(StatedSL 4 F)) (hα : α * α = 1)
    (hout : ∀ k : ↥(StatedSL 4 F), α ≠ MulAut.conj k) :
    GoodFixedCentral (Nat.card F = 3) α ∨ IsReflection (StatedSL 4 F) α ∨
      IsGraphLike (StatedSL 4 F) α := by
  rcases lin_involution_form hF α hα with ⟨A, ⟨c, hA⟩, hact⟩ | ⟨A, hAt, hact⟩
  · rcases classify_inner hF α A c hA hact hout with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨A, hAt, hact⟩)

end CFSG.GH74.Generic.S1
