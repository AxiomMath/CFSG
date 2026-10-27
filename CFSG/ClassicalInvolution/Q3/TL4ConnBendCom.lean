module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Bend

open Subgroup
open scoped Pointwise

@[expose] def BigCommT (P : Type*) [Group P] : Prop :=
  ∀ x z : P, (∀ y : P, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z) → ∀ y : P, Commute x y

theorem BigCommT.of_mulEquiv {P P' : Type*} [Group P] [Group P'] (e : P ≃* P')
    (h : BigCommT P') : BigCommT P := by
  intro x z hxz y
  have h' := h (e x) (e z) fun y' => by
    obtain ⟨y, rfl⟩ := e.surjective y'
    rcases hxz y with h1 | h1
    · left
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1, map_one]
    · right
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1]
  have := (h' (e y)).map e.symm.toMonoidHom
  simpa using this

theorem BigCommT.of_commute {P : Type*} [Group P] (h : ∀ x y : P, Commute x y) : BigCommT P :=
  fun x _ _ y => h x y

theorem bigCommT_sylow_of_one {X : Type*} [Group X] [Finite X] (Q₀ : Sylow 2 X)
    (h : BigCommT ↥(Q₀ : Subgroup X)) : ∀ Q : Sylow 2 X, BigCommT ↥(Q : Subgroup X) := by
  intro Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X Q₀ Q
  have hcoe : ((g • Q₀ : Sylow 2 X) : Subgroup X) =
      (Q₀ : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  rw [hcoe]
  exact BigCommT.of_mulEquiv
    ((Q₀ : Subgroup X).equivMapOfInjective _ (MulAut.conj g).injective).symm h

theorem bigCommT_sylow_of_mulEquiv {X X' : Type*} [Group X] [Group X'] [Finite X] (e : X ≃* X')
    (h : ∀ Q : Sylow 2 X', BigCommT ↥(Q : Subgroup X')) :
    ∀ Q : Sylow 2 X, BigCommT ↥(Q : Subgroup X) := by
  intro Q
  have := h (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
  exact BigCommT.of_mulEquiv ((Q : Subgroup X).equivMapOfInjective _ e.injective) this

end CFSG.ClassicalInvolution.Q3.TL4.Bend
