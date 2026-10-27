module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AltGeneric

public section

namespace CFSG.QuasithinUnique.Setup.X3
open Equiv CFSG.QuasithinUnique

set_option maxRecDepth 100000

@[expose] def relStab {n : ℕ} (b : Fin n → ℕ) : Subgroup (Perm (Fin n)) where
  carrier := {σ | ∀ i j, b i = b j ↔ b (σ i) = b (σ j)}
  mul_mem' := by
    intro σ τ hσ hτ i j
    exact (hτ i j).trans (hσ (τ i) (τ j))
  one_mem' := fun _ _ => Iff.rfl
  inv_mem' := by
    intro σ hσ i j
    have := hσ (σ⁻¹ i) (σ⁻¹ j)
    simpa using this.symm

instance {n : ℕ} (b : Fin n → ℕ) : DecidablePred (· ∈ relStab b) := fun σ =>
  decidable_of_iff (∀ i j, b i = b j ↔ b (σ i) = b (σ j)) Iff.rfl

@[expose] def blkX7 (i : Fin 7) : ℕ := if i.val < 6 then 0 else 1

@[expose] def blkY7 (i : Fin 7) : ℕ := if i.val < 4 then 0 else 1

@[expose] def blkX8 (i : Fin 8) : ℕ := i.val / 4

@[expose] def blkY8 (i : Fin 8) : ℕ := i.val / 2

end CFSG.QuasithinUnique.Setup.X3
