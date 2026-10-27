module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aLocal

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

section Gram

variable {F : Type*} [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2]

@[expose] def gram : Matrix (Fin 8) (Fin 8) k :=
  Matrix.of fun r s =>
    ((Xm (Pi.single r 1) : Matrix (Fin 3) (Fin 3) k) * Xm (Pi.single s 1)).trace

@[expose] def sigma8 : Fin 8 → Fin 8 := ![7, 6, 4, 5, 2, 3, 1, 0]

theorem sigma8_sigma8 (r : Fin 8) : sigma8 (sigma8 r) = r := by
  revert r
  decide

theorem gram_apply (r s : Fin 8) : gram k r s = if s = sigma8 r then 1 else 0 := by
  have h2 := two_eq_zero_k k
  fin_cases r <;> fin_cases s <;>
    simp [gram, Xm, sigma8, Matrix.trace, Fin.sum_univ_three, Pi.single_apply]
  all_goals (rw [one_add_one_eq_two]; exact h2)

theorem gram_mul_self : gram k * gram k = 1 := by
  ext r s
  rw [Matrix.mul_apply, Finset.sum_eq_single (sigma8 r)]
  · simp [gram_apply, sigma8_sigma8, Matrix.one_apply, eq_comm]
  · intro t _ ht
    simp [gram_apply, ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CharP k 2] in
theorem gram_transpose : (gram k)ᵀ = gram k := by
  ext r s
  simp only [Matrix.transpose_apply, gram, Matrix.of_apply]
  rw [Matrix.trace_mul_comm]

omit [CharP k 2] in
theorem Xm_eq_sum (c : Fin 8 → k) :
    (Xm c : Matrix (Fin 3) (Fin 3) k) = ∑ r, c r • Xm (Pi.single r (1 : k)) := by
  have hc : c = ∑ r, c r • (Pi.single r (1 : k) : Fin 8 → k) := by
    ext t
    simp [Finset.sum_apply, Pi.single_apply]
  calc (Xm c : Matrix (Fin 3) (Fin 3) k) = XmL k c := rfl
    _ = XmL k (∑ r, c r • (Pi.single r (1 : k) : Fin 8 → k)) := by rw [← hc]
    _ = ∑ r, c r • Xm (Pi.single r (1 : k)) := by simp [map_sum, map_smul, XmL_apply]

omit [CharP k 2] in
theorem trace_Xm_mul_Xm (c c' : Fin 8 → k) :
    ((Xm c : Matrix (Fin 3) (Fin 3) k) * Xm c').trace = ∑ r, ∑ s, c r * c' s * gram k r s := by
  rw [Xm_eq_sum k c, Xm_eq_sum k c', Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_smul, gram]
  simp [mul_assoc]

theorem conjMat_mul_conjMat (i : ℕ) (g : SL(3, F)) (X Y : Matrix (Fin 3) (Fin 3) k) :
    conjMat k i g X * conjMat k i g Y = conjMat k i g (X * Y) := by
  simp only [conjMat]
  calc twistMat k i g * X * twistMat k i g⁻¹ * (twistMat k i g * Y * twistMat k i g⁻¹)
      = twistMat k i g * X * (twistMat k i g⁻¹ * twistMat k i g) * Y * twistMat k i g⁻¹ := by
        simp only [mul_assoc]
    _ = twistMat k i g * (X * Y) * twistMat k i g⁻¹ := by
        rw [twistMat_inv_mul, mul_one]
        simp only [mul_assoc]

theorem Xm_adjRep_col (i : ℕ) (g : SL(3, F)) (s : Fin 8) :
    Xm (fun r => adjRep k i g r s) = conjMat k i g (Xm (Pi.single s (1 : k))) := by
  have h : (fun r => adjRep k i g r s) = co (conjMat k i g (Xm (Pi.single s (1 : k)))) := by
    funext r
    exact adjRep_apply k i g r s
  rw [h]
  exact Xm_co k (by rw [trace_conjMat, trace_Xm])

theorem adjRep_gram_invariant (i : ℕ) (g : SL(3, F)) :
    (adjRep k i g)ᵀ * gram k * adjRep k i g = gram k := by
  ext s t
  have h1 : ((Xm (fun r => adjRep k i g r s) : Matrix (Fin 3) (Fin 3) k) *
      Xm (fun r => adjRep k i g r t)).trace = gram k s t := by
    rw [Xm_adjRep_col, Xm_adjRep_col, conjMat_mul_conjMat, trace_conjMat]
    rfl
  rw [trace_Xm_mul_Xm] at h1
  rw [← h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  refine Finset.sum_congr rfl (fun r' _ => ?_)
  ring

theorem gram_adjRep_dual (i : ℕ) (g : SL(3, F)) :
    gram k * (adjRep k i g⁻¹)ᵀ = adjRep k i g * gram k := by
  set A := adjRep k i g with hA
  set B := adjRep k i g⁻¹ with hB
  have hAB : A * B = 1 := by rw [hA, hB, ← map_mul, mul_inv_cancel, map_one]
  have hBt : Bᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  have hGG := gram_mul_self k
  have h1 : Aᵀ * gram k * A = gram k := adjRep_gram_invariant k i g
  have h2 : gram k * A = Bᵀ * gram k := by
    calc gram k * A = (Bᵀ * Aᵀ) * gram k * A := by rw [hBt, one_mul]
      _ = Bᵀ * (Aᵀ * gram k * A) := by simp only [mul_assoc]
      _ = Bᵀ * gram k := by rw [h1]
  have h3 : gram k * (gram k * A) * gram k = gram k * (Bᵀ * gram k) * gram k := by rw [h2]
  have e1 : gram k * (gram k * A) * gram k = A * gram k := by
    rw [← mul_assoc (gram k) (gram k) A, hGG, one_mul]
  have e2 : gram k * (Bᵀ * gram k) * gram k = gram k * Bᵀ := by
    calc gram k * (Bᵀ * gram k) * gram k = gram k * Bᵀ * (gram k * gram k) := by
          simp only [mul_assoc]
      _ = gram k * Bᵀ := by rw [hGG, mul_one]
  rw [e1, e2] at h3
  exact h3.symm

end Gram

end CFSG.QuasithinUnique.Setup.X7a
