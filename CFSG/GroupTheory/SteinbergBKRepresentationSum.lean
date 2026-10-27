module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.GroupTheory.SteinbergBK

variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V] [Module F V]

@[expose] def fixedSubspace (ρ : G →* LinearMap.GeneralLinearGroup F V) (A : Subgroup G) :
    Submodule F V where
  carrier := {v | ∀ a ∈ A, (ρ a : V →ₗ[F] V) v = v}
  add_mem' := fun hv hw a ha => by rw [map_add, hv a ha, hw a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := fun c v hv a ha => by rw [map_smul, hv a ha]

theorem representation_subgroup_sum_invariants' (ρ : G →* LinearMap.GeneralLinearGroup F V)
    (A : Subgroup G) [Fintype A] :
    (∀ a ∈ A, (ρ a : V →ₗ[F] V) * (∑ b : A, (ρ b : V →ₗ[F] V)) = ∑ b : A, (ρ b : V →ₗ[F] V)) ∧
    LinearMap.range (∑ b : A, (ρ b : V →ₗ[F] V)) ≤ fixedSubspace ρ A := by
  have hinv : ∀ a ∈ A, (ρ a : V →ₗ[F] V) * ∑ b : A, (ρ b : V →ₗ[F] V) =
      ∑ b : A, (ρ b : V →ₗ[F] V) := by
    intro a ha
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨a, ha⟩ : A)) _ _ fun b => ?_
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Units.val_mul]
  refine ⟨hinv, ?_⟩
  rintro _ ⟨w, rfl⟩ a ha
  rw [← Module.End.mul_apply, hinv a ha]

end CFSG.GroupTheory.SteinbergBK
