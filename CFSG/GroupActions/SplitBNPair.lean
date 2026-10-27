module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

public section

namespace CFSG.GroupActions

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def SplitBN (B N U : Subgroup G) {I : Type*} (n : I → N) : Prop :=
  ∃ _ : ((B ⊓ N).subgroupOf N).Normal,
    B ⊔ N = ⊤ ∧
    Function.Injective (fun i => (n i : N ⧸ (B ⊓ N).subgroupOf N)) ∧
    (∀ i, orderOf (n i : N ⧸ (B ⊓ N).subgroupOf N) = 2) ∧
    Subgroup.closure (Set.range fun i => (n i : N ⧸ (B ⊓ N).subgroupOf N)) = ⊤ ∧
    (∀ i, ∀ x ∈ N, {((n i : N) : G)} * (B : Set G) * {x} ⊆
      (B : Set G) * {((n i : N) : G) * x} * (B : Set G) ∪ (B : Set G) * {x} * (B : Set G)) ∧
    (∀ i, ¬ {((n i : N) : G)} * (B : Set G) * {((n i : N) : G)⁻¹} ⊆ (B : Set G)) ∧
    U ≤ B ∧ (U.subgroupOf B).Normal ∧ Group.IsNilpotent U ∧
    (∀ x ∈ B ⊓ N, ∀ y ∈ B ⊓ N, x * y = y * x) ∧
    (B : Set G) = (U : Set G) * ((B ⊓ N : Subgroup G) : Set G) ∧
    U ⊓ (B ⊓ N) = ⊥

end CFSG.GroupActions
