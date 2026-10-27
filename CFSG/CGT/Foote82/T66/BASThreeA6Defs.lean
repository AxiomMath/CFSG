module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.CGT.Foote82

@[expose] def InvolAutA6Cases : Prop :=
  ∀ θ : MulAut (alternatingGroup (Fin 6)), (∀ g, θ (θ g) = g) → (∃ g, θ g ≠ g) →
    (∃ g : alternatingGroup (Fin 6), orderOf (θ g * g⁻¹) = 4) ∨
    (∃ a b g : alternatingGroup (Fin 6), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ a * b = b * a ∧
      b ∉ Subgroup.zpowers a ∧ ((θ a = a⁻¹ ∧ θ b = b) ∨ (θ a = b ∧ θ b = a)) ∧
      orderOf (θ g * g⁻¹) = 2)

end CFSG.CGT.Foote82
