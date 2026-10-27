module

public import CFSG.GH74.Generic.S1.LinClassify
public import CFSG.GH74.Generic.S1.LinGraph

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank

theorem classify_lin_full {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (α : MulAut ↥(StatedSL 4 F)) (hα : α * α = 1)
    (hout : ∀ k : ↥(StatedSL 4 F), α ≠ MulAut.conj k) :
    GoodFixedCentral (Nat.card F = 3) α ∨ IsReflection (StatedSL 4 F) α ∨
      IsExoticLin (StatedSL 4 F) α := by
  rcases classify_lin hF α hα hout with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases graphLike_lin hF α hα h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

end CFSG.GH74.Generic.S1
