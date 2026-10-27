module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup

variable {G : Type*} [Group G]

@[expose] def IP_outer (x : G) (T Rd : Subgroup G) : Prop :=
  ∀ u ∈ T, u * u = 1 → u ∉ Rd →
    ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({x} : Set G) ∧ IsElemAb2 E ∧ Nat.card E = 16

@[expose] def IP_cent_four (T P Q Rd : Subgroup G) : Prop :=
  ∀ V : Subgroup G, V ≤ P → IsFour V →
    ∃ W : Subgroup G, W ≤ T ∧ W ⊓ Rd = Q ∧
      (∀ v ∈ V, ∀ w ∈ W, v * w * v⁻¹ ∈ W) ∧
      ∀ d ∈ T, (∀ v ∈ V, d * v = v * d) → ∃ v ∈ V, ∃ w ∈ W, d = v * w

@[expose] def IP_Rd_factor (T P Q Rd : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ T ∧ B ⊓ Rd = P ⊔ Q ∧ B ⊔ Rd = T

@[expose] def IP_Rd_cyclic (T Rd : Subgroup G) : Prop :=
  ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Rd

@[expose] def IP_P_four (P : Subgroup G) : Prop :=
  ∃ V : Subgroup G, V ≤ P ∧ IsFour V

@[expose] def IP_P_conj (x z : G) (P : Subgroup G) : Prop :=
  ∀ a ∈ P, a * a = 1 → a ≠ 1 → ∃ c ∈ Subgroup.centralizer ({x} : Set G), c * a * c⁻¹ = z

@[expose] def IP_P_trans (P Q Rd : Subgroup G) : Prop :=
  ∀ u ∈ Rd, u ∉ P ⊔ Q → u * u = 1 → ∀ a ∈ P, ∀ b ∈ P,
    (a * u) * (a * u) = 1 → (b * u) * (b * u) = 1 → ∃ p ∈ P, p * (a * u) * p⁻¹ = b * u

@[expose] def IP_cent_Rd (P Q Rd : Subgroup G) : Prop :=
  ∀ d ∈ Rd, (∀ p ∈ P, d * p = p * d) → d ∈ P ⊔ Q

@[expose] def IP_cent_P_exp (T P Q : Subgroup G) : Prop :=
  ∀ t ∈ T, (∀ p ∈ P, t * p = p * t) → t * t ∈ Q

end CFSG.GH74.GLS.Stage1.Thm6.Sec12
