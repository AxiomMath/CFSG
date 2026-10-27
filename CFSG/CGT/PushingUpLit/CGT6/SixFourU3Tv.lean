module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

section Tv

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] noncomputable def sqNorm3 (a : Fin 3 → K) : K := ∑ j, h.bar (a j) * a j

@[expose] noncomputable def tvM (a : Fin 3 → K) (c : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + c • vecMulVec a (fun j => h.bar (a j))

theorem tvM_apply (a : Fin 3 → K) (c : K) (i j : Fin 3) :
    tvM h a c i j = (if i = j then 1 else 0) + c * (a i * h.bar (a j)) := by
  simp [tvM, Matrix.one_apply, vecMulVec_apply]

theorem tvM_zero (a : Fin 3 → K) : tvM h a 0 = 1 := by
  simp [tvM]

theorem sqNorm3_eq_dot (a : Fin 3 → K) : sqNorm3 h a = (fun j => h.bar (a j)) ⬝ᵥ a := rfl

theorem tvM_mul (a : Fin 3 → K) (ha : sqNorm3 h a = 0) (c c' : K) :
    tvM h a c * tvM h a c' = tvM h a (c + c') := by
  have hP : vecMulVec a (fun j => h.bar (a j)) * vecMulVec a (fun j => h.bar (a j)) = 0 := by
    rw [vecMulVec_mul_vecMulVec, ← sqNorm3_eq_dot, ha]
    simp
  unfold tvM
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hP, smul_zero,
    add_zero, add_smul]
  abel

theorem tvM_map_transpose (a : Fin 3 → K) (c : K) :
    ((tvM h a c).map h.bar)ᵀ = tvM h a (h.bar c) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, tvM_apply, map_add, map_mul, h.bar_bar]
  by_cases hij : i = j
  · subst hij
    simp [mul_comm]
  · have : j ≠ i := fun e => hij e.symm
    simp [hij, this, mul_comm]

theorem tvM_unitary (a : Fin 3 → K) (ha : sqNorm3 h a = 0) (c : K) (hc : c + h.bar c = 0) :
    ((tvM h a c).map h.bar)ᵀ * tvM h a c = 1 := by
  rw [tvM_map_transpose, tvM_mul h a ha, add_comm, hc, tvM_zero]

theorem det_tvM (a : Fin 3 → K) (c : K) : (tvM h a c).det = 1 + c * sqNorm3 h a := by
  have e : tvM h a c = 1 + replicateCol Unit a * replicateRow Unit (c • fun j => h.bar (a j)) := by
    ext i j
    simp [tvM, Matrix.mul_apply, vecMulVec_apply]
  rw [e, det_one_add_replicateCol_mul_replicateRow]
  simp only [sqNorm3, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => by ring

@[expose] noncomputable def tvGL (a : Fin 3 → K) (ha : sqNorm3 h a = 0) (c : K) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (tvM h a c) (by
    rw [det_tvM, ha, mul_zero, add_zero]
    exact one_ne_zero)

theorem coe_tvGL (a : Fin 3 → K) (ha : sqNorm3 h a = 0) (c : K) :
    ((tvGL h a ha c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = tvM h a c := rfl

theorem tvGL_mem (a : Fin 3 → K) (ha : sqNorm3 h a = 0) (c : K) (hc : c + h.bar c = 0) :
    tvGL h a ha c ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h, coe_tvGL, det_tvM, ha, mul_zero, add_zero]
  exact ⟨rfl, tvM_unitary h a ha c hc⟩

theorem conj_tvM (γ : GL (Fin 3) K)
    (hγ : ((γ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (γ : Matrix (Fin 3) (Fin 3) K) = 1)
    (a : Fin 3 → K) (c : K) :
    (γ : Matrix (Fin 3) (Fin 3) K) * tvM h a c * ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      tvM h ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ a) c := by
  have hinv : ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((γ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hγ
  rw [hinv]
  have hvec : (fun j => h.bar (a j)) ᵥ* ((γ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ =
      fun j => h.bar (((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ a) j) := by
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, mul_comm]
  have hγγ : (γ : Matrix (Fin 3) (Fin 3) K) * ((γ : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 :=
    _root_.mul_eq_one_comm.mpr hγ
  unfold tvM
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hγγ, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hvec]

end Tv

end CFSG.CGT.PushingUpLit.CGT6
