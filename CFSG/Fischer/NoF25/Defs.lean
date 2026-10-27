module

public import Mathlib.Data.Set.Card

public section

namespace CFSG.Fischer

@[expose] def inducedPerms {Y : Type*} [Group Y] (C : Set Y) : Set (Equiv.Perm C) :=
  {σ | ∃ r : Y, ∀ x : C, (σ x : Y) = r * x * r⁻¹}

@[expose] def fixSets {α : Type*} (S : Set (Equiv.Perm α)) (k : ℕ) : Set (Set α) :=
  {F | ∃ σ ∈ S, σ * σ = 1 ∧ F = {x | σ x = x} ∧ F.ncard = k}

end CFSG.Fischer
