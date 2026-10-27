module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup
open scoped commutatorElement

section Operators

variable {G : Type*} [Group G]

@[expose] def IsElemAbelian (p : ℕ) (E : Subgroup G) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ p = 1

@[expose] def Om1 (H : Subgroup G) : Subgroup G := Subgroup.closure {h | h ∈ H ∧ h ^ 2 = 1}

@[expose] def Om2 (H : Subgroup G) : Subgroup G := Subgroup.closure {h | h ∈ H ∧ h ^ 4 = 1}

@[expose] def O2 (A : Subgroup G) : Subgroup G :=
  ⨆ N : {N : Subgroup G // N ≤ A ∧ A ≤ normalizer (N : Set G) ∧ IsPGroup 2 N}, N.1

@[expose] def O2res (A : Subgroup G) : Subgroup G :=
  ⨅ N : {N : Subgroup G // N ≤ A ∧ A ≤ normalizer (N : Set G) ∧ ∃ k : ℕ, N.relIndex A = 2 ^ k}, N.1

end Operators

section Complements

variable {G : Type*} [Group G]

@[expose] def ComplementsConj (E H : Subgroup G) : Prop :=
  ∀ K : Subgroup G, K ⊓ E = ⊥ → K ⊔ E = H ⊔ E → ∃ e ∈ E, ∀ g : G, g ∈ K ↔ e⁻¹ * g * e ∈ H

@[expose] def ActsFreely (p : ℕ) (H E : Subgroup G) : Prop :=
  ∃ B : Finset G, (∀ b ∈ B, b ∈ E) ∧ Subgroup.closure (B : Set G) = E ∧ Nat.card E = p ^ B.card ∧
    (∀ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ B) ∧ ∀ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ = b → h = 1

@[expose] def FreeSection (p : ℕ) (H N M : Subgroup G) : Prop :=
  N ≤ M ∧ (∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N) ∧ (∀ a ∈ M, a ^ p ∈ N) ∧
    (∀ h ∈ H, ∀ g ∈ N, h * g * h⁻¹ ∈ N) ∧ (∀ h ∈ H, ∀ g ∈ M, h * g * h⁻¹ ∈ M) ∧
    ∃ B : Finset G, (∀ b ∈ B, b ∈ M) ∧ Subgroup.closure (B : Set G) ⊔ N = M ∧
      N.relIndex M = p ^ B.card ∧
      (∀ h ∈ H, ∀ b ∈ B, ∃ b' ∈ B, (h * b * h⁻¹)⁻¹ * b' ∈ N) ∧
      ∀ h ∈ H, ∀ b ∈ B, (h * b * h⁻¹)⁻¹ * b ∈ N → h = 1

@[expose] def FreeSec2 (x : G) (N M : Subgroup G) : Prop :=
  N ≤ M ∧ (∀ a ∈ M, ∀ b ∈ M, ⁅a, b⁆ ∈ N) ∧ (∀ a ∈ M, a ^ 2 ∈ N) ∧
    (∀ g ∈ N, x * g * x⁻¹ ∈ N) ∧ (∀ g ∈ M, x * g * x⁻¹ ∈ M) ∧
    Nat.card {m : G // m ∈ M ∧ m⁻¹ * (x * m * x⁻¹) ∈ N} ^ 2 = Nat.card M * Nat.card N

end Complements

end CFSG.GH74.GLS.Bg.TwoGroups
