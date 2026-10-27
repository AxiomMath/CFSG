module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

@[expose] def Fz59Linear {G : Type} [Group G] (T₃ : Subgroup G) : Prop :=
  ∀ χ : G → Prop,
    (∀ g ∈ T₃, ∀ a ∈ T₃, (χ (g * a * g⁻¹) ↔ χ a)) →
    (∀ a ∈ T₃, ∀ c ∈ T₃, a * a = 1 → c * c = 1 → a * c = c * a → a ≠ 1 → c ≠ 1 → a ≠ c →
      (Xor (χ a) (χ c) ↔ χ (a * c))) →
    ∃ M : Subgroup G, M ≤ T₃ ∧ (M = T₃ ∨ M.relIndex T₃ = 2) ∧
      ∀ v ∈ T₃, v * v = 1 → v ≠ 1 → (χ v ↔ v ∉ M)

end CFSG.OddStandard.SmallF3.FritzII
