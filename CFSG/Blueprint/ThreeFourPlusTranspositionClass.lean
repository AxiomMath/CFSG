module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Blueprint

@[expose] def ThreeFourPlusClass (H : Type*) [Group H] (D : Set H) : Prop :=
  (∃ d₀ : H, D = Set.range fun h : H => h⁻¹ * d₀ * h) ∧
    (∀ d ∈ D, orderOf d = 2) ∧
    Subgroup.closure D = ⊤ ∧
    (∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ)) ∧
    ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) = 4 → a⁻¹ * b⁻¹ * a * b ∈ D

end CFSG.Blueprint
