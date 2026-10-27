module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open Matrix CFSG.Open

namespace Sp6

section Block

variable {K : Type} [Field K]

@[expose] def blkMat (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (diagonal fun i => M i 0 0) (diagonal fun i => M i 0 1)
    (diagonal fun i => M i 1 0) (diagonal fun i => M i 1 1)

theorem blkMat_mul (M N : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    blkMat M * blkMat N = blkMat (fun i => M i * N i) := by
  simp only [blkMat, fromBlocks_multiply, diagonal_mul_diagonal, ← diagonal_add]
  congr 1 <;> congr 1 <;> funext i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem blkMat_one : blkMat (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  simp only [blkMat, fromBlocks_one.symm]
  congr 1 <;> simp

theorem blkMat_injective :
    Function.Injective (blkMat : (Fin 3 → Matrix (Fin 2) (Fin 2) K) → _) := by
  intro M N h
  funext i
  have h1 := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have h2 := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  have h3 := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
  have h4 := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
  simp [blkMat] at h1 h2 h3 h4
  ext p q
  fin_cases p <;> fin_cases q <;> simpa

theorem blkMat_symplectic (M : Fin 3 → Matrix (Fin 2) (Fin 2) K) (hM : ∀ i, (M i).det = 1) :
    (blkMat M)ᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) * blkMat M =
      fromBlocks 0 1 (-1) 0 := by
  simp only [blkMat, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.one_mul]
  have hd : ∀ i, M i 0 0 * M i 1 1 - M i 0 1 * M i 1 0 = 1 := fun i => by
    rw [← Matrix.det_fin_two (M i)]; exact hM i
  have key : ∀ f g : Fin 3 → K, -(diagonal f) + diagonal g = diagonal (fun i => g i - f i) := by
    intro f g
    rw [neg_add_eq_sub, ← diagonal_sub]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, ← diagonal_zero]
    congr 1
    funext i
    simp [mul_comm]
  · rw [key, ← diagonal_one]
    congr 1
    funext i
    have := hd i
    linear_combination this
  · rw [key, ← diagonal_one, diagonal_neg]
    congr 1
    funext i
    have := hd i
    linear_combination (-1 : K) * this
  · rw [key, ← diagonal_zero]
    congr 1
    funext i
    simp [mul_comm]

@[expose] def blkGL : (Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) →* GL (Fin 3 ⊕ Fin 3) K where
  toFun M :=
    { val := blkMat fun i =>
        ((M i : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      inv := blkMat fun i =>
        (((M i)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [blkMat_mul]
        simp_rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
        exact blkMat_one
      inv_val := by
        rw [blkMat_mul]
        simp_rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
        exact blkMat_one }
  map_one' := by
    apply Units.ext
    simp only [Units.val_one, Matrix.SpecialLinearGroup.coe_one, Pi.one_apply]
    exact blkMat_one
  map_mul' M N := by
    apply Units.ext
    simp only [Units.val_mul, Pi.mul_apply, Matrix.SpecialLinearGroup.coe_mul]
    exact (blkMat_mul _ _).symm

theorem coe_blkGL (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    ((blkGL M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      blkMat fun i => ((M i : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blkGL_injective : Function.Injective (blkGL (K := K)) := by
  intro M N h
  have h' := congrArg
    (fun g : GL (Fin 3 ⊕ Fin 3) K => (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) h
  simp only [coe_blkGL] at h'
  have := blkMat_injective h'
  funext i
  exact Subtype.ext (congrFun this i)

theorem blkGL_mem_statedSp (M : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) K) :
    blkGL M ∈ StatedSp 3 K := by
  rw [StatedAPI.mem_statedSp_iff, coe_blkGL]
  exact blkMat_symplectic _ fun i => (M i).2

end Block

end Sp6

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
