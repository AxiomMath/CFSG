module

public import CFSG.LinearAlgebra.F2CubeModule
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LinearAlgebra.F2Cube

variable {n : ℕ}

@[expose] def fixedCount (M : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ :=
  Fintype.card {v : Fin n → ZMod 2 // M.mulVec v = v}

@[expose] def fixedDim (M : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ :=
  Nat.log 2 (fixedCount M)

theorem fixedCount_eq_two_pow_finrank (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    fixedCount M = 2 ^ CFSG.StandardType.D4Rank.fixDim (Matrix.mulVecLin M) := by
  have h1 : fixedCount M = Nat.card (LinearMap.ker (Matrix.mulVecLin M - 1)) := by
    unfold fixedCount
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, Module.End.one_apply,
      sub_eq_zero]
  rw [h1, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem fixedDim_eq_finrank (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    fixedDim M = CFSG.StandardType.D4Rank.fixDim (Matrix.mulVecLin M) := by
  unfold fixedDim
  rw [fixedCount_eq_two_pow_finrank, Nat.log_pow (by norm_num)]

structure FixedFreeRep (n : ℕ) where
  toFun : C3 → Matrix (Fin n) (Fin n) (ZMod 2)
  map_zero : toFun 0 = 1
  map_add : ∀ s t, toFun (s + t) = toFun s * toFun t
  eq_zero_of_fixed : ∀ v : Fin n → ZMod 2, (∀ t, (toFun t).mulVec v = v) → v = 0

instance : CoeFun (FixedFreeRep n) (fun _ => C3 → Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ⟨FixedFreeRep.toFun⟩

@[expose] noncomputable def FixedFreeRep.toCubeRep (ρ : FixedFreeRep n) :
    CubeRep (Fin n → ZMod 2) where
  toFun t := Matrix.mulVecLin (ρ t)
  map_zero := by
    rw [ρ.map_zero]
    exact Matrix.mulVecLin_one
  map_add s t := by
    rw [ρ.map_add]
    exact Matrix.mulVecLin_mul _ _

theorem FixedFreeRep.eps_toCubeRep (ρ : FixedFreeRep n) : ρ.toCubeRep.eps = 0 :=
  ρ.toCubeRep.eps_eq_zero fun v hv => ρ.eq_zero_of_fixed v hv

theorem FixedFreeRep.sum_fixedDim (ρ : FixedFreeRep n) :
    ∑ t ∈ Finset.univ.filter (fun t : C3 => t ≠ 0), fixedDim (ρ t) = 8 * n := by
  have h := ρ.toCubeRep.sum_fixDim ρ.eps_toCubeRep
  rw [Module.finrank_pi, Fintype.card_fin] at h
  rw [← h]
  exact Finset.sum_congr rfl fun t _ => fixedDim_eq_finrank _

theorem FixedFreeRep.exists_conj (ρ σ : FixedFreeRep n)
    (h : ∀ t, t ≠ 0 → fixedCount (ρ t) = fixedCount (σ t)) :
    ∃ E F : Matrix (Fin n) (Fin n) (ZMod 2), F * E = 1 ∧ E * F = 1 ∧ ∀ t, E * ρ t = σ t * E := by
  obtain ⟨e, he⟩ := ρ.toCubeRep.exists_equiv σ.toCubeRep ρ.eps_toCubeRep σ.eps_toCubeRep rfl
    (fun g hg => by
      have h1 := h g hg
      rw [fixedCount_eq_two_pow_finrank, fixedCount_eq_two_pow_finrank] at h1
      exact Nat.pow_right_injective (le_refl 2) h1)
  have hcomp : ∀ t,
      e.toLinearMap ∘ₗ Matrix.mulVecLin (ρ t) = Matrix.mulVecLin (σ t) ∘ₗ e.toLinearMap :=
    fun t => LinearMap.ext fun w => he t w
  refine ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · intro t
    have h1 := congrArg LinearMap.toMatrix' (hcomp t)
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply',
      ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h1
    exact h1

end CFSG.LinearAlgebra.F2Cube
