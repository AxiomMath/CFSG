module

public import CFSG.ClassicalGroups.Orthogonal.SumSquaresDefs
public import CFSG.Open.PGLModelDefs
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Matrix

theorem mem_orthogonalGroup_sumSqForm_of_transpose_mul_self {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] {A : GL ι K} (h : (A : Matrix ι ι K)ᵀ * A = 1) :
    A ∈ CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)) := by
  rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
  intro v
  change ((A : Matrix ι ι K) *ᵥ v) ⬝ᵥ ((A : Matrix ι ι K) *ᵥ v) = v ⬝ᵥ v
  rw [← Matrix.dotProduct_transpose_mulVec (A := (A : Matrix ι ι K)) (x := v)
    (y := (A : Matrix ι ι K) *ᵥ v)]
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem permutationGL_mem_orthogonalGroup_sumSqForm {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (σ : Equiv.Perm ι) :
    TauCeti.permutationGL (k := K) σ ∈
      CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)) := by
  refine mem_orthogonalGroup_sumSqForm_of_transpose_mul_self ?_
  rw [TauCeti.permutationGL_coe, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem negCoordGL_mem_orthogonalGroup_sumSqForm {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (s : Finset ι) :
    negCoordGL (K := K) s ∈ CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)) := by
  refine mem_orthogonalGroup_sumSqForm_of_transpose_mul_self ?_
  have ht : (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) *
      (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) = 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  have h1 : TauCeti.diagGL (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) *
      TauCeti.diagGL (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) = 1 := by
    rw [← TauCeti.diagGL.map_mul, ht, TauCeti.diagGL.map_one]
  have hT : ((TauCeti.diagGL (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) : GL ι K) :
      Matrix ι ι K)ᵀ =
      TauCeti.diagGL (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) := by
    rw [TauCeti.diagGL_coe, Matrix.diagonal_transpose]
  change ((TauCeti.diagGL (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) : GL ι K) :
      Matrix ι ι K)ᵀ *
    (TauCeti.diagGL (fun i : ι => if i ∈ s then (-1 : Kˣ) else 1) : GL ι K) = 1
  rw [hT, ← Units.val_mul, h1, Units.val_one]

theorem sq_apply_self_eq_one_of_mem {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    {g : GL ι K} (hg : g ∈ CFSG.PGLModel.orthogonalGroup (sumSqForm (ι := ι) (K := K)))
    (hd : ∀ i j : ι, i ≠ j → (g : Matrix ι ι K) i j = 0) (i : ι) :
    (g : Matrix ι ι K) i i ^ 2 = 1 := by
  have hcol : (g : Matrix ι ι K) *ᵥ Pi.single i 1 =
      Pi.single i ((g : Matrix ι ι K) i i) := by
    rw [Matrix.mulVec_single_one]
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · rw [Pi.single_eq_of_ne hji, Matrix.col_apply, hd j i hji]
  have hsingle : ∀ a : K, sumSqForm (Pi.single i a) = a * a := by
    intro a
    simp only [sumSqForm, single_dotProduct, Pi.single_eq_same]
  have hv := (CFSG.PGLModel.mem_orthogonalGroup_iff.mp hg) (Pi.single i 1)
  rw [hcol, hsingle, hsingle, mul_one] at hv
  simpa [pow_two] using hv

end CFSG.ClassicalGroups.Orthogonal
