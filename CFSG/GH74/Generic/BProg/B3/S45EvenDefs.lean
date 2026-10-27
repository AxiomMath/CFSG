module

public import CFSG.GH74.Generic.BProg.B3.S45TableA

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.GH74.Generic.BProg.B3.S45TableA

@[expose] def EvenEA (X : Type) [Group X] (y : MulAut X) : Prop :=
  (∀ s : X, y s = s → ∀ k : ℕ, s ^ (2 ^ k) = 1 → s ^ 2 = 1) ∨
    ∃ t : X, t * t = 1 ∧ t ∉ Subgroup.center X ∧ ∀ g : X, y g = t * g * t⁻¹

@[expose] def S45EvenTableEA : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsQuasisimple X → IsPGroup 2 ↥(Subgroup.center X) →
    Subgroup.center X ≠ ⊥ → GHList (X ⧸ Subgroup.center X) → ∀ y : MulAut X, orderOf y = 2 →
    Datum X y →
    (∀ T : Subgroup X, IsPGroup 2 ↥T → (∀ t ∈ T, y t = t) → ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) →
    EvenEA X y →
    NativeSporadic.IsSporadic (X ⧸ Subgroup.center X) .M12

end CFSG.GH74.Generic.BProg.B3
