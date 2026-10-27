module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9InnerBlock

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.SeitzReduction.LinearPilot CFSG.StandardType.SUTorus

variable {K : Type} [Field K]

@[expose] def IsBlockDiag {d : ℕ} (S : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) K) : Prop :=
  ∀ i j, (i ∈ S ∧ j ∉ S) ∨ (i ∉ S ∧ j ∈ S) → M i j = 0

theorem isBlockDiag_iff_commute {d : ℕ} (S : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) K) :
    IsBlockDiag S M ↔ M * blockComplProj S = blockComplProj S * M := by
  constructor
  · intro h
    ext i j
    rw [blockComplProj, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · simp [hi, hj]
    · simp only [hi, hj, if_true, if_false, mul_one, mul_zero, zero_mul, one_mul]
      exact h i j (Or.inl ⟨hi, hj⟩)
    · simp only [hi, hj, if_true, if_false, mul_one, mul_zero, zero_mul, one_mul]
      exact (h i j (Or.inr ⟨hi, hj⟩)).symm
    · simp [hi, hj]
  · intro h i j hij
    rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have h1 := congrFun (congrFun (congrArg (fun X : Matrix (Fin d) (Fin d) K => X) h) i) j
      rw [blockComplProj, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      simpa [hi, hj] using h1
    · have h1 := congrFun (congrFun (congrArg (fun X : Matrix (Fin d) (Fin d) K => X) h) i) j
      rw [blockComplProj, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      simpa [hi, hj] using h1.symm

theorem isBlockDiag_inv {d : ℕ} {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K)) :
    IsBlockDiag S ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  rw [isBlockDiag_iff_commute] at hM ⊢
  have h2 : ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      (M : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : (M : Matrix (Fin d) (Fin d) K) *
      ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hbPa : (M : Matrix (Fin d) (Fin d) K) * blockComplProj S *
      ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blockComplProj S := by
    rw [hM, mul_assoc, h3, Matrix.mul_one]
  calc ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * blockComplProj S
      = ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        ((M : Matrix (Fin d) (Fin d) K) * blockComplProj S *
          ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by rw [hbPa]
    _ = (((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (M : Matrix (Fin d) (Fin d) K) * blockComplProj S) *
        ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [← mul_assoc ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          ((M : Matrix (Fin d) (Fin d) K) * blockComplProj S)
          ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K),
          ← mul_assoc ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          (M : Matrix (Fin d) (Fin d) K) (blockComplProj S)]
    _ = blockComplProj S * ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [h2, Matrix.one_mul]

theorem blockRes_mul_of_left {d : ℕ} {S : Finset (Fin d)}
    {M N : Matrix (Fin d) (Fin d) K} (hM : IsBlockDiag S M) :
    blockRes S (M * N) = blockRes S M * blockRes S N := by
  ext a b
  simp only [blockRes, Matrix.mul_apply]
  set e := S.equivFin.symm with he
  have hz : ∀ k ∉ S, M (e a) k * N k (e b) = 0 := by
    intro k hk
    rw [hM (e a) k (Or.inl ⟨(e a).2, hk⟩), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e fun k : ↥S => M (e a) k * N k (e b)).symm

theorem blockRes_mul_of_right {d : ℕ} {S : Finset (Fin d)}
    {M N : Matrix (Fin d) (Fin d) K} (hN : IsBlockDiag S N) :
    blockRes S (M * N) = blockRes S M * blockRes S N := by
  ext a b
  simp only [blockRes, Matrix.mul_apply]
  set e := S.equivFin.symm with he
  have hz : ∀ k ∉ S, M (e a) k * N k (e b) = 0 := by
    intro k hk
    rw [hN k (e b) (Or.inr ⟨hk, (e b).2⟩), mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e fun k : ↥S => M (e a) k * N k (e b)).symm

theorem isBlockOn_conj_of_isBlockDiag {d : ℕ} {S : Finset (Fin d)} {M : GL (Fin d) K}
    (hM : IsBlockDiag S (M : Matrix (Fin d) (Fin d) K))
    {u : Matrix (Fin d) (Fin d) K} (hu : IsBlockOn S u) :
    IsBlockOn S ((M : Matrix (Fin d) (Fin d) K) * u *
      ((M⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
  refine isBlockOn_conj ((isBlockDiag_iff_commute S _).mp hM) ?_ ?_ hu
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
