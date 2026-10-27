module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CMatLin
public import Mathlib.Data.Matrix.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {n : ℕ}

theorem A6CSimMat.mul {M N : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M)
    (hN : A6CSimMat N) : A6CSimMat (M * N) := by
  have h : M * N * (M * N).transpose = M * (N * N.transpose) * M.transpose := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  unfold A6CSimMat at hM hN ⊢
  rw [h]
  rcases hN with hN | hN <;> rw [hN]
  · rw [Matrix.mul_one]
    exact hM
  · rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul]
    rcases hM with hM | hM <;> rw [hM]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)

theorem A6CSimMat.one : A6CSimMat (1 : Matrix (Fin n) (Fin n) (ZMod 3)) :=
  Or.inl (by rw [Matrix.transpose_one, Matrix.mul_one])

theorem A6CSimMat.neg {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) :
    A6CSimMat (-M) := by
  unfold A6CSimMat at hM ⊢
  rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact hM

theorem A6CSimMat.transpose {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) :
    A6CSimMat M.transpose := by
  unfold A6CSimMat at hM ⊢
  rw [Matrix.transpose_transpose]
  rcases hM with h | h
  · exact Or.inl (mul_eq_one_comm.mp h)
  · refine Or.inr ?_
    have h1 : M * (-M.transpose) = 1 := by rw [Matrix.mul_neg, h, neg_neg]
    have h2 : -M.transpose * M = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.neg_mul] at h2
    exact neg_eq_iff_eq_neg.mp h2

theorem A6CSimMat.pow {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) (k : ℕ) :
    A6CSimMat (M ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact A6CSimMat.one
  | succ k ih => rw [pow_succ]; exact ih.mul hM

structure A6CModel (n : ℕ) (Γ : Type) [Group Γ] where
  ofMat : Matrix (Fin n) (Fin n) (ZMod 3) → Γ
  ofMat_mul : ∀ M N, A6CSimMat M → A6CSimMat N → ofMat (M * N) = ofMat M * ofMat N
  ofMat_eq : ∀ M N, A6CSimMat M → A6CSimMat N → (ofMat M = ofMat N ↔ M = N ∨ M = -N)
  ofMat_surj : ∀ x : Γ, ∃ M, A6CSimMat M ∧ ofMat M = x

namespace A6CModel

variable {Γ : Type} [Group Γ] (m : A6CModel n Γ)

theorem ofMat_one : m.ofMat 1 = 1 := by
  have h := m.ofMat_mul 1 1 A6CSimMat.one A6CSimMat.one
  rw [Matrix.mul_one] at h
  exact mul_left_cancel (a := m.ofMat 1) (by rw [mul_one]; exact h.symm)

theorem ofMat_neg {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) :
    m.ofMat (-M) = m.ofMat M :=
  (m.ofMat_eq (-M) M hM.neg hM).mpr (Or.inr rfl)

theorem ofMat_pow {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) (k : ℕ) :
    m.ofMat (M ^ k) = m.ofMat M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact m.ofMat_one
  | succ k ih => rw [pow_succ, pow_succ, m.ofMat_mul _ _ (hM.pow k) hM, ih]

theorem ofMat_transpose {M : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M) :
    m.ofMat M.transpose = (m.ofMat M)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← m.ofMat_mul M M.transpose hM hM.transpose]
  rcases hM with h | h
  · rw [h]
    exact m.ofMat_one
  · rw [h, m.ofMat_neg A6CSimMat.one]
    exact m.ofMat_one

theorem ofMat_conj {M N : Matrix (Fin n) (Fin n) (ZMod 3)} (hM : A6CSimMat M)
    (hN : A6CSimMat N) :
    m.ofMat (M * N * M.transpose) = m.ofMat M * m.ofMat N * (m.ofMat M)⁻¹ := by
  rw [m.ofMat_mul _ _ (hM.mul hN) hM.transpose, m.ofMat_mul _ _ hM hN, m.ofMat_transpose hM]

end A6CModel

end CFSG.OddStandard.SmallF3.Omega
