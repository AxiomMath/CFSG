module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Asc77

@[expose] def AutAlphaPairs (X : Type) [Group X] : Prop :=
  ∀ (𝒳 : Subgroup (MulAut X)) (hinn : ∀ g : X, MulAut.conj g ∈ 𝒳) (a a' : X),
    a * a = 1 → a ≠ 1 → a' ≠ a → a * a' = a' * a → (∃ g : X, g * a * g⁻¹ = a') →
      alphaOf (Subgroup.closure
        ({⟨MulAut.conj a, hinn a⟩, ⟨MulAut.conj a', hinn a'⟩} : Set ↥𝒳)) = ⊥

end CFSG.ClassicalInvolution.Q3.TL4
