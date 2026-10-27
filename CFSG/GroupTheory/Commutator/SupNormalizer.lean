module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {A B U : Subgroup G}

theorem commutator_sup_eq_commutator_left
    (hBnorm : B ≤ Subgroup.normalizer (A : Set G))
    (hBcent : B ≤ Subgroup.centralizer (U : Set G)) :
    ⁅A ⊔ B, U⁆ = ⁅A, U⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono le_sup_left le_rfl)
  refine (Subgroup.commutator_le).mpr ?_
  intro p hp u hu
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hBnorm
  have hp' : p ∈ (A : Set G) * (B : Set G) := by rwa [← hset]
  rcases Set.mem_mul.mp hp' with ⟨a, ha, b, hb, rfl⟩
  have hbcomm : b * u = u * b :=
    (Subgroup.mem_centralizer_iff.mp (hBcent hb) u hu).symm
  have hbu : b * u * b⁻¹ = u := by
    rw [show b * u * b⁻¹ = (b * u) * b⁻¹ from rfl, hbcomm]
    group
  have hcomm : ⁅a * b, u⁆ = ⁅a, u⁆ := by
    rw [commutatorElement_def]
    rw [show (a * b) * u * (a * b)⁻¹ * u⁻¹ = a * (b * u * b⁻¹) * a⁻¹ * u⁻¹ by group,
      hbu, commutatorElement_def]
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator ha hu

end CFSG
