module

public import CFSG.GH74.GLS.Stage1.Thm6.Prelude
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G]

@[expose] def Is3 (f : G) : Prop := ∃ k : ℕ, f ^ 3 ^ k = 1

@[expose] def IP_f3 (x : G) (P : Subgroup G) : Prop :=
  ∀ V : Subgroup G, V ≤ P → IsFour V → ∃ f : G, Is3 f ∧ f * x = x * f ∧
    (∀ v ∈ V, f * v * f⁻¹ ∈ V) ∧ ∃ v ∈ V, f * v * f⁻¹ ≠ v

@[expose] def IP_z_V (z : G) (P : Subgroup G) : Prop :=
  ∀ V : Subgroup G, V ≤ P → IsFour V → z ∈ V

@[expose] def IP_E8_two (T : Subgroup G) : Prop :=
  (∃ E : Subgroup G, E ≤ T ∧ IsElemAb2 E ∧ Nat.card E = 8 ∧ ∀ t ∈ T, ∀ e ∈ E, t * e * t⁻¹ ∈ E) →
  ∀ E₁ E₂ E₃ : Subgroup G, E₁ ≤ T → E₂ ≤ T → E₃ ≤ T → IsElemAb2 E₁ → IsElemAb2 E₂ →
    IsElemAb2 E₃ → Nat.card E₁ = 8 → Nat.card E₂ = 8 → Nat.card E₃ = 8 →
    E₁ = E₂ ∨ E₁ = E₃ ∨ E₂ = E₃

@[expose] def IV3_12_8c_sylow (x : G) (S T P : Subgroup G) : Prop :=
  T.relIndex S = 2 → ∀ V : Subgroup G, V ≤ P → IsFour V →
    (∃ a ∈ S, a ∉ T ∧
      a ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) →
    IsSylow2In (S ⊓ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))
      (Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G))

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
