module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Data

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def e6Pair (u v : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ k, v k * ∑ j, Tag.E6.cartan k j * u j

@[expose] def e6KerP (i : Fin 3) (v : Fin Tag.E6.rank → ℤ) : ℤ :=
  e6Pair (e6A2Simple₀ i) v + e6Pair (e6A2Simple₁ i) v

@[expose] def e6KerQ (i : Fin 3) (v : Fin Tag.E6.rank → ℤ) : ℤ :=
  e6Pair (e6A2Simple₁ i) v

@[expose] def e6Eig (z : ℤ × ℤ) : Option (Bool × Fin 3) :=
  if z = (1, 0) then some (true, 0) else
  if z = (0, 1) then some (true, 1) else
  if z = (-1, -1) then some (true, 2) else
  if z = (-1, 0) then some (false, 0) else
  if z = (0, -1) then some (false, 1) else
  if z = (1, 1) then some (false, 2) else none

@[expose] def e6BlockVal (z : ℤ × ℤ) : Prop :=
  z = (2, 1) ∨ z = (1, 2) ∨ z = (1, -1) ∨ z = (-2, -1) ∨ z = (-1, -2) ∨ z = (-1, 1)

instance (z : ℤ × ℤ) : Decidable (e6BlockVal z) := by unfold e6BlockVal; infer_instance

theorem e6_root_kinds : ∀ v ∈ rootFinset .E6,
    ((e6KerP 0 v, e6KerQ 0 v) = (0, 0) ∧ (e6KerP 1 v, e6KerQ 1 v) = (0, 0)) ∨
    (e6BlockVal (e6KerP 0 v, e6KerQ 0 v) ∧ (e6KerP 1 v, e6KerQ 1 v) = (0, 0)) ∨
    ((e6KerP 0 v, e6KerQ 0 v) = (0, 0) ∧ e6BlockVal (e6KerP 1 v, e6KerQ 1 v)) ∨
    (∃ σ : Bool, ∃ j k : Fin 3, e6Eig (e6KerP 0 v, e6KerQ 0 v) = some (σ, j) ∧
      e6Eig (e6KerP 1 v, e6KerQ 1 v) = some (!σ, k)) := by
  decide +kernel

@[expose] def e6BlockRootsF (i : Fin 3) : Finset (Fin Tag.E6.rank → ℤ) :=
  (rootFinset .E6).filter fun v => ∃ a b : Fin 3, a ≠ b ∧ v = e6A2Root i a b

@[expose] def e6MixedRootsF (s : Fin 3) : Finset (Fin Tag.E6.rank → ℤ) :=
  (rootFinset .E6).filter fun v => ∃ σ : Bool, ∃ j k : Fin 3,
    e6Eig (e6KerP 0 v, e6KerQ 0 v) = some (σ, j) ∧
      e6Eig (e6KerP 1 v, e6KerQ 1 v) = some (!σ, k) ∧ j - k = s

@[expose] def e6BlockRoots (i : Fin 3) : Set (Fin Tag.E6.rank → ℤ) := ↑(e6BlockRootsF i)

@[expose] def e6MixedRoots (s : Fin 3) : Set (Fin Tag.E6.rank → ℤ) := ↑(e6MixedRootsF s)

theorem e6_block2_iff : ∀ v ∈ rootFinset .E6, (∃ a b : Fin 3, a ≠ b ∧ v = e6A2Root 2 a b) ↔
    ((e6KerP 0 v, e6KerQ 0 v) = (0, 0) ∧ (e6KerP 1 v, e6KerQ 1 v) = (0, 0)) := by
  decide +kernel

theorem e6_block0_iff : ∀ v ∈ rootFinset .E6, (∃ a b : Fin 3, a ≠ b ∧ v = e6A2Root 0 a b) ↔
    (e6BlockVal (e6KerP 0 v, e6KerQ 0 v) ∧ (e6KerP 1 v, e6KerQ 1 v) = (0, 0)) := by
  decide +kernel

theorem e6_block1_iff : ∀ v ∈ rootFinset .E6, (∃ a b : Fin 3, a ≠ b ∧ v = e6A2Root 1 a b) ↔
    ((e6KerP 0 v, e6KerQ 0 v) = (0, 0) ∧ e6BlockVal (e6KerP 1 v, e6KerQ 1 v)) := by
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube
