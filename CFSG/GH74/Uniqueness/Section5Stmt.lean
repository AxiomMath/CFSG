module

public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

structure Prop52Cond (Z : Set X) (M : Subgroup X) (p : ℕ) (P : Subgroup X) : Prop where
  pgroup : IsPGroup p P
  three_le : 3 ≤ (omegaFix M (P : Set X)).ncard
  exists_u : ∃ u ∈ Z, u ∈ normalizer (P : Set X) ∧ zCosetNum Z P u = zNumShare Z M p

@[expose] def Prop52Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup X, Maximal (Prop52Cond Z M p) P →
    ((∃ s ∈ Z, s ∈ normalizer (P : Set X)) ∧
      ∀ s ∈ Z, s ∈ normalizer (P : Set X) → ∀ β ∈ omega M, conjugate β s = β → P ≤ β) ∧
    (DoublyTransitive M → ∀ γ ∈ omegaFix M (P : Set X),
      ∃ s ∈ Z, s ∈ normalizer (P : Set X) ∧ conjugate γ s = γ)

@[expose] def Cor57Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ¬ DoublyTransitive M → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∃ s ∈ Z, ∃ Q : Subgroup X, IsPGroup p Q ∧ 3 ≤ (omegaFix M (Q : Set X)).ncard ∧
      s ∈ normalizer (Q : Set X) ∧ zCosetNum Z Q s = zNumShare Z M p ∧
      ∀ β ∈ omega M, conjugate β s = β → Q ≤ β) ∧
    (∃ s ∈ Z, ∃ Q : Subgroup X, IsPGroup p Q ∧ 3 ≤ (omegaFix M (Q : Set X)).ncard ∧
      s ∈ normalizer (Q : Set X) ∧ zCosetNum Z Q s = zNumShare Z M p ∧
      ∃ β ∈ omegaFix M (Q : Set X), conjugate β s ≠ β ∧
        ABGLocalTools.IsSylowOf p Q (β ⊓ conjugate β s))

end CFSG.GH74.Uniqueness
