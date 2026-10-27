module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInvolution
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module
open exteriorPower
open scoped TensorProduct

variable {K : Type*} [Field K] [CharP K 2]

private theorem finrank_ker_tensor_one_left {W : Type*} [AddCommGroup W] [Module K W]
    (S : W →ₗ[K] W) :
    Module.finrank K (LinearMap.ker
      (TensorProduct.map (1 : K →ₗ[K] K) S - 1)) =
      Module.finrank K (LinearMap.ker (S - 1)) := by
  let Φ : (K ⊗[K] W) ≃ₗ[K] W := TensorProduct.lid K W
  have h : ∀ x, Φ (TensorProduct.map (1 : K →ₗ[K] K) S x) = S (Φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r w => simp [Φ, TensorProduct.map_tmul, TensorProduct.lid_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  exact (CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining
    Φ (TensorProduct.map (1 : K →ₗ[K] K) S) S h).symm
