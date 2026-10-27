module

public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X]

structure Prop74Spec (Z : Set X) (M : Subgroup X) (z : X) (W : Subgroup X)
    (Γ : Set (Subgroup X)) : Prop where
  subset : Γ ⊆ omegaFix M (W : Set X)
  base_mem : M ∈ Γ
  one_lt_ncard : 1 < Γ.ncard
  conjugate_mem : ∀ β ∈ Γ, conjugate β z ∈ Γ
  centralizer_le : ∀ β ∈ Γ, ∀ γ ∈ Γ, β ≠ γ →
    centralizer (CFSG.OddInversion.invertedSet W z : Set X) ⊓ β ⊓ γ ≤ M
  exists_involution : ∀ β ∈ Γ, β ≠ M → ∃ t ∈ Z, conjugate M t = β ∧
    conjSet (CFSG.OddInversion.invertedSet W z) (z⁻¹ * t * z) ⊆
      ((M ⊓ β ⊓ conjugate β z : Subgroup X) : Set X) ∧
    centralizer (conjSet (CFSG.OddInversion.invertedSet W z) (z⁻¹ * t * z)) ⊓ M ⊓ β ≤
      M ⊓ β ⊓ conjugate β z ∧
    ∃ g : X, conjugate (conjugate β z) g = M ∧ conjugate β g ∈ Γ

end CFSG.GH74.Uniqueness
