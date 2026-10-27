module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinOutQ8
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSpAut

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution CFSG.GH74.L5U5 Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem sMat_adjugate (X : Matrix (Fin 2) (Fin 2) F) :
    !![0, -1; 1, 0] * X * !![0, 1; -1, 0] = (adjugate X)ᵀ := by
  rw [adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem trace_adjugate_two (X : Matrix (Fin 2) (Fin 2) F) : (adjugate X).trace = X.trace := by
  rw [adjugate_fin_two, trace_fin_two, trace_fin_two]
  simp [add_comm]

theorem trace_blk4 (X Y : Matrix (Fin 2) (Fin 2) F) : (blk4 X Y).trace = X.trace + Y.trace := by
  have h : (blk4 X Y).trace = (fromBlocks X 0 0 Y).trace := by
    have := Equiv.sum_comp (finSumFinEquiv (m := 2) (n := 2)) (fun i => (blk4 X Y) i i)
    simp only [Matrix.trace, Matrix.diag]
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock, reindex_apply]
  rw [h]
  simp [Matrix.trace, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem blk4_transpose (X Y : Matrix (Fin 2) (Fin 2) F) : (blk4 X Y)ᵀ = blk4 Xᵀ Yᵀ := by
  rw [blk4_eq_reindex, blk4_eq_reindex]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.transpose_reindex, fromBlocks_transpose,
    transpose_zero]

theorem blk4_map (σ : F ≃+* F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    (blk4 X Y).map σ = blk4 (X.map σ) (Y.map σ) := by
  rw [blk4_eq_reindex, blk4_eq_reindex]
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, ← Matrix.submatrix_map,
    fromBlocks_map, Matrix.map_zero _ (map_zero σ)]

theorem trace_blk4_one_map (σ : F ≃+* F) (x : F) :
    ((blk4 !![x, -1; 1, 0] 1).map σ).trace = σ x + 2 := by
  rw [blk4_map, trace_blk4, Matrix.map_one _ (map_zero σ) (map_one σ)]
  simp [trace_fin_two]

variable (F) in
@[expose] def slBlk : SL(2, F) × SL(2, F) →* SL(4, F) where
  toFun x := ⟨blk4 x.1 x.2, by rw [det_blk4, x.1.2, x.2.2, one_mul]⟩
  map_one' := Subtype.ext blk4_one
  map_mul' x y := Subtype.ext (blk4_mul _ _ _ _).symm

theorem coe_slBlk (x : SL(2, F) × SL(2, F)) :
    ((slBlk F x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = blk4 x.1 x.2 := rfl

theorem trace_blk4_companion (x : F) : (blk4 !![x, -1; 1, 0] 1).trace = x + 2 := by
  rw [trace_blk4]
  simp [trace_fin_two]

theorem trace_map_two (σ : F ≃+* F) (X : Matrix (Fin 2) (Fin 2) F) :
    (X.map σ).trace = σ X.trace := by
  simp [trace_fin_two]

theorem sMat_sq : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sInv_sq : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sInv_mul_sMat : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sMat_mul_sInv : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sInv_transpose : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, 1; -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem sMat_transpose : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem blkScalar_transpose (c d : F) : (blkScalar c d)ᵀ = blkScalar c d := by
  rw [blkScalar, blk4_transpose, Matrix.scalar_apply, Matrix.scalar_apply, diagonal_transpose,
    diagonal_transpose]

theorem blkScalar_inv_eq {c d : F} {N : Matrix (Fin 4) (Fin 4) F} (h : blkScalar c d * N = 1) :
    c ≠ 0 ∧ d ≠ 0 ∧ N = blkScalar c⁻¹ d⁻¹ := by
  have hdet := congrArg Matrix.det h
  rw [det_mul, blkScalar, det_blk4, Matrix.scalar_apply, Matrix.scalar_apply, det_diagonal,
    det_diagonal, det_one] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hc : c ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  have hd : d ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  refine ⟨hc, hd, ?_⟩
  calc N = blkScalar c⁻¹ d⁻¹ * blkScalar c d * N := by
        rw [blkScalar_mul, inv_mul_cancel₀ hc, inv_mul_cancel₀ hd, blkScalar_one, Matrix.one_mul]
    _ = blkScalar c⁻¹ d⁻¹ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

open CFSG.ComponentClassification.CatFactsSp4 in
theorem exists_blkScalar_of_comm (h2 : (2 : F) ≠ 0) {B : Matrix (Fin 4) (Fin 4) F}
    (hB : ∀ a b : SL(2, F), (a = 1 ∨ b = 1) →
      B * blk4 (a : Matrix (Fin 2) (Fin 2) F) b = blk4 (a : Matrix (Fin 2) (Fin 2) F) b * B) :
    ∃ c d : F, B = blkScalar c d := by
  have h1 := hB negOneSL 1 (Or.inr rfl)
  rw [coe_negOneSL, Matrix.SpecialLinearGroup.coe_one] at h1
  obtain ⟨P, Q, rfl⟩ := exists_blk4_of_comm h2 h1
  let u : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hP : ∀ s : SL(2, F), P * s = s * P := fun s => by
    have := hB s 1 (Or.inr rfl)
    rw [Matrix.SpecialLinearGroup.coe_one, blk4_mul, blk4_mul, Matrix.mul_one,
      Matrix.one_mul] at this
    exact (blk4_inj this).1
  have hQ : ∀ s : SL(2, F), Q * s = s * Q := fun s => by
    have := hB 1 s (Or.inl rfl)
    rw [Matrix.SpecialLinearGroup.coe_one, blk4_mul, blk4_mul, Matrix.mul_one,
      Matrix.one_mul] at this
    exact (blk4_inj this).2
  exact ⟨P 0 0, Q 0 0, by rw [blkScalar, ← eq_scalar_of_comm_transvections (hP u) (hP l),
    ← eq_scalar_of_comm_transvections (hQ u) (hQ l)]⟩

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
