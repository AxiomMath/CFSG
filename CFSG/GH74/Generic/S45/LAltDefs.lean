module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup

variable {n : ℕ}

@[expose] def centAlt (σ : Perm (Fin n)) : Subgroup (Perm (Fin n)) :=
  alternatingGroup (Fin n) ⊓ centralizer ({σ} : Set (Perm (Fin n)))

theorem mem_centAlt {σ g : Perm (Fin n)} :
    g ∈ centAlt σ ↔ g ∈ alternatingGroup (Fin n) ∧ g * σ = σ * g := by
  rw [centAlt, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem sigma_sq_apply {σ : Perm (Fin n)} (hσ : σ * σ = 1) (x : Fin n) : σ (σ x) = x := by
  simpa using congrArg (fun p : Perm (Fin n) => p x) hσ

@[expose] def IsDblTransp (g : Perm (Fin n)) : Prop :=
  ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ g = swap a b * swap c d

@[expose] def BadCent (σ : Perm (Fin n)) : Prop :=
  (∃ g ∈ centAlt σ, orderOf g = 4) ∧
    ∃ X : Subgroup (Perm (Fin n)), X ≤ centAlt σ ∧ ⁅X, X⁆ = X ∧
      ∃ g ∈ X, orderOf g = 4 ∨ IsDblTransp g

end CFSG.GH74.Generic.S45.LAlt
