module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ComponentClassification.SolMax

open Subgroup Equiv

@[expose] def SignalizerNineEightFusionInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (H : Subgroup X)
    (φ : ↥H →* alternatingGroup (Fin 9) × Multiplicative (ZMod 2)),
    Function.Surjective φ → Odd (Nat.card φ.ker) →
    ∀ (t : X) (htH : t ∈ H), t * t = 1 → φ ⟨t, htH⟩ = (1, Multiplicative.ofAdd 1) →
    centralizer ({t} : Set X) ≤ H →
    (∀ (x : X) (hx : x ∈ H), x * t = t * x →
      ((φ ⟨x, hx⟩).1 : Perm (Fin 9)).support.card = 4 → ∀ g : X, g⁻¹ * t * g ≠ x) →
    ∀ (s g : X) (hsH : s ∈ H), g⁻¹ * t * g = s →
      ((φ ⟨s, hsH⟩).1 : Perm (Fin 9)).support.card = 8 → False

end CFSG.ComponentClassification.SolMax
