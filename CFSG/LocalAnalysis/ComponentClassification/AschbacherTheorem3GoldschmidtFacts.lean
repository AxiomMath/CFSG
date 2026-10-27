module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs

public section

open CFSG.Open
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem3

@[expose] def GoldschmidtTypeAutomorphisms : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P E : Subgroup Y),
    IsSimpleGroup X → goldschmidtSimpleType (X ⧸ Subgroup.center X) →
    IsSylowOf 2 P X → IsElemAbelian 2 E →
    E ≤ Subgroup.normalizer (X : Set Y) → E ≤ Subgroup.normalizer (P : Set Y) →
    (∀ e ∈ E, ∀ x ∈ omegaOne P, e * x = x * e) →
    (∀ e ∈ E, ∀ p ∈ P, e⁻¹ * p⁻¹ * e * p ∈ omegaOne P) →
    Nat.card E ≤ Nat.card (omegaOne P) *
      Nat.card (E ⊓ Subgroup.centralizer (X : Set Y) : Subgroup Y)

@[expose] def GoldschmidtTypeGeneration : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P : Subgroup Y),
    IsSimpleGroup X → goldschmidtSimpleType (X ⧸ Subgroup.center X) → IsSylowOf 2 P X →
    (∃ n : ℕ, IsBenderType X n) ∨
    X ≤ ⨆ z : {z : Y // z ∈ P ∧ z ^ 2 = 1 ∧ z ≠ 1}, X ⊓ Subgroup.centralizer {(z : Y)}

structure Theorem3KnownGroupFacts : Prop where
  goldschmidt_type_automorphisms : GoldschmidtTypeAutomorphisms
  goldschmidt_type_generation : GoldschmidtTypeGeneration

end CFSG.ComponentClassification.AschbacherTheorem3
