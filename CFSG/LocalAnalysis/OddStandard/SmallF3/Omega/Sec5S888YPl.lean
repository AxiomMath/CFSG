module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.SmallF3.Omega

structure IsPlanes {Y : Type} [Group Y] (D : Subgroup Y) (W : Fin 4 → Subgroup Y) : Prop where
  comm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a
  sq : ∀ a ∈ D, a * a = 1
  card_D : Nat.card D = 2 ^ 8
  le : ∀ i, W i ≤ D
  card : ∀ i, Nat.card (W i) = 4
  decomp : ∀ d ∈ D, ∃ w : Fin 4 → Y, (∀ i, w i ∈ W i) ∧ d = w 0 * w 1 * w 2 * w 3

structure IsPlaneAuts {Y : Type} [Group Y] (D : Subgroup Y) (W : Fin 4 → Subgroup Y)
    (τ : Fin 4 → Y ≃* Y) : Prop where
  cube : ∀ i y, τ i (τ i (τ i y)) = y
  mem_D : ∀ i, ∀ d ∈ D, τ i d ∈ D
  mem_W : ∀ i, ∀ w ∈ W i, τ i w ∈ W i
  triv : ∀ i j, i ≠ j → ∀ w ∈ W j, τ i w = w
  fpf : ∀ i, ∀ w ∈ W i, w ≠ 1 → τ i w ≠ w

end CFSG.OddStandard.SmallF3.Omega
