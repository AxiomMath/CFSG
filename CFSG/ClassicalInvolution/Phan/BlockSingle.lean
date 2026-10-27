module

public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.Phan

variable {F : Type*} [Field F]

theorem blockMat_one_add_single {m k s : ℕ} (h : s + k ≤ m) (a b : Fin k) (t : F) :
    blockMat m s (1 + Matrix.single a b t) =
      1 + Matrix.single (⟨s + a.val, by have := a.isLt; omega⟩ : Fin m)
        (⟨s + b.val, by have := b.isLt; omega⟩ : Fin m) t := by
  unfold blockMat
  have : (1 + Matrix.single a b t) - 1 = Matrix.single a b t := by abel
  rw [this]
  congr 1
  ext x y
  simp only [Matrix.mul_apply, Matrix.single_apply, blockSel_apply, Matrix.transpose_apply]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single a]
    · simp only [and_self, ite_true, Fin.ext_iff]
      by_cases hx : x.val = s + a.val <;> by_cases hy : y.val = s + b.val <;>
        simp [hx, hy, eq_comm]
    · intro j₁ _ hj₁
      simp [hj₁.symm]
    · simp
  · intro j _ hj
    simp [hj.symm]
  · simp

end CFSG.ClassicalInvolution.Phan
