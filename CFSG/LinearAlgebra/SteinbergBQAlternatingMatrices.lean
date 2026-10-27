module

public import CFSG.LinearAlgebra.SteinbergBQShearGroup
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def altR (x y : V) : Dual (ZMod 2) V →ₗ[ZMod 2] V :=
  (Dual.eval (ZMod 2) V y).smulRight x + (Dual.eval (ZMod 2) V x).smulRight y

theorem altR_apply (x y : V) (f : Dual (ZMod 2) V) : altR x y f = f y • x + f x • y :=
  rfl

theorem altR_comm (x y : V) : altR x y = altR y x :=
  LinearMap.ext fun f => by rw [altR_apply, altR_apply, add_comm]

theorem altR_add_left (x x' y : V) : altR (x + x') y = altR x y + altR x' y :=
  LinearMap.ext fun f => by
    simp only [altR_apply, LinearMap.add_apply, map_add, smul_add, add_smul]
    abel

theorem altR_add_right (x y y' : V) : altR x (y + y') = altR x y + altR x y' := by
  rw [altR_comm, altR_add_left, altR_comm y, altR_comm y']

theorem altR_smul_left (c : ZMod 2) (x y : V) : altR (c • x) y = c • altR x y :=
  LinearMap.ext fun f => by
    simp only [altR_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_add, smul_smul,
      mul_comm]

theorem altR_smul_right (c : ZMod 2) (x y : V) : altR x (c • y) = c • altR x y := by
  rw [altR_comm, altR_smul_left, altR_comm]

@[expose] def altRₗ (x : V) : V →ₗ[ZMod 2] Dual (ZMod 2) V →ₗ[ZMod 2] V where
  toFun := altR x
  map_add' := altR_add_right x
  map_smul' c y := altR_smul_right c x y

@[expose] def altAct (h : V ≃ₗ[ZMod 2] V) (T : Dual (ZMod 2) V →ₗ[ZMod 2] V) :
    Dual (ZMod 2) V →ₗ[ZMod 2] V :=
  (h : V →ₗ[ZMod 2] V) ∘ₗ T ∘ₗ (h : V →ₗ[ZMod 2] V).dualMap

@[expose] def fixedSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (Λ : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 2) W where
  carrier := {z | ∀ μ ∈ Λ, μ z = z}
  add_mem' {z z'} hz hz' μ hμ := by rw [map_add, hz μ hμ, hz' μ hμ]
  zero_mem' μ _ := map_zero μ
  smul_mem' c z hz μ hμ := by rw [map_smul, hz μ hμ]

theorem mem_fixedSub {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {Λ : Subgroup (W ≃ₗ[ZMod 2] W)} {z : W} : z ∈ fixedSub Λ ↔ ∀ μ ∈ Λ, μ z = z :=
  Iff.rfl

end CFSG.LinearAlgebra.SteinbergBQ

