module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Combinatorics.SimpleGraph.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Subgroup

variable (G : Type*) [Group G] (p : ℕ)

@[expose] def sylowNormalizers : Set (Subgroup G) :=
  {B₀ | ∃ T : Sylow p G, normalizer ((T : Subgroup G) : Set G) = B₀}

@[expose] def maximalParabolics : Set (Subgroup G) :=
  {M | IsCoatom M ∧ ∃ B₀ ∈ sylowNormalizers G p, B₀ ≤ M}

@[expose] def extremalParabolics : Set (Subgroup G) :=
  {M | M ∈ maximalParabolics G p ∧ ∀ M' ∈ maximalParabolics G p, M.index ≤ M'.index}

@[expose] def parabolicGraph : SimpleGraph (extremalParabolics G p) where
  Adj M N := M ≠ N ∧ ∃ B₀ ∈ sylowNormalizers G p, B₀ ≤ (M : Subgroup G) ⊓ (N : Subgroup G)
  symm := ⟨fun _ _ ⟨hne, B₀, hB₀, hle⟩ => ⟨hne.symm, B₀, hB₀, by rwa [inf_comm]⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

variable {G p}

theorem mem_sylowNormalizers {B₀ : Subgroup G} :
    B₀ ∈ sylowNormalizers G p ↔ ∃ T : Sylow p G, normalizer ((T : Subgroup G) : Set G) = B₀ :=
  Iff.rfl

theorem mem_maximalParabolics {M : Subgroup G} :
    M ∈ maximalParabolics G p ↔ IsCoatom M ∧ ∃ B₀ ∈ sylowNormalizers G p, B₀ ≤ M :=
  Iff.rfl

theorem mem_extremalParabolics {M : Subgroup G} :
    M ∈ extremalParabolics G p ↔
      M ∈ maximalParabolics G p ∧ ∀ M' ∈ maximalParabolics G p, M.index ≤ M'.index :=
  Iff.rfl

theorem parabolicGraph_adj {M N : extremalParabolics G p} :
    (parabolicGraph G p).Adj M N ↔
      M ≠ N ∧ ∃ B₀ ∈ sylowNormalizers G p, B₀ ≤ (M : Subgroup G) ⊓ (N : Subgroup G) :=
  Iff.rfl

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
