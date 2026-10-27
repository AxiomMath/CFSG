module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup

structure FrameModel (Λ : Type) [Group Λ] (E : Subgroup Λ) (z : Λ) (O : Fin 5 → Set Λ) :
    Prop where
  z_mem : z ∈ E
  z_ne_one : z ≠ 1
  card_N : Nat.card (normalizer (E : Set Λ)) = 2 ^ 11 * 443520
  isOrbit : ∀ i, ∃ x ∈ E, O i = {y | ∃ n ∈ normalizer (E : Set Λ), n * x * n⁻¹ = y}
  ncard : ∀ i, (O i).ncard = ![22, 22, 231, 231, 1540] i
  disjoint : ∀ i j, i ≠ j → Disjoint (O i) (O j)
  not_mem_one : ∀ i, (1 : Λ) ∉ O i
  not_mem_z : ∀ i, z ∉ O i
  cover : ∀ v ∈ E, v ≠ 1 → v = z ∨ ∃ i, v ∈ O i
  swap : O 1 = (fun u => z * u) '' O 0
  prod : ∀ u ∈ O 0, ∀ u' ∈ O 0, u ≠ u' → u * u' ∈ O 2
  gen : Subgroup.closure (insert z (O 0)) = E
  frameAut : ∀ α : E ≃* E, (∀ e : E, (e : Λ) = z → (α e : Λ) = z) →
    (∀ e : E, (e : Λ) ∈ O 0 → (α e : Λ) ∈ O 0) →
    ∃ n ∈ normalizer (E : Set Λ), ∀ e : E, (α e : Λ) = n * e * n⁻¹

end CFSG.EvenSporadicStandard.TwoFi22.DS81
