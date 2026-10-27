module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.ClassicalGroups.Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def transv (c : V) (φ : Module.Dual K V) : V →ₗ[K] V :=
  LinearMap.id + φ.smulRight c

theorem transv_apply (c : V) (φ : Module.Dual K V) (x : V) :
    transv c φ x = x + φ x • c := by
  simp [transv, LinearMap.smulRight_apply]

theorem transv_transv_neg_apply {c : V} {φ : Module.Dual K V} (hφ : φ c = 0) (x : V) :
    transv c φ (transv c (-φ) x) = x := by
  have h : φ (transv c (-φ) x) = φ x := by
    rw [transv_apply, map_add, map_smul, hφ, smul_zero, add_zero]
  rw [transv_apply c φ (transv c (-φ) x), h, transv_apply c (-φ) x, LinearMap.neg_apply]
  module

theorem transv_neg_transv_apply {c : V} {φ : Module.Dual K V} (hφ : φ c = 0) (x : V) :
    transv c (-φ) (transv c φ x) = x := by
  have h : (-φ) (transv c φ x) = -φ x := by
    rw [LinearMap.neg_apply, transv_apply, map_add, map_smul, hφ, smul_zero, add_zero]
  rw [transv_apply c (-φ) (transv c φ x), h, transv_apply c φ x]
  module

end CFSG.ClassicalGroups.Linear
