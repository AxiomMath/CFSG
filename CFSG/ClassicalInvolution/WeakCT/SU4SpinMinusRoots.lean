module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusRep

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra QuadraticMap
  CFSG.LieType.Universal.Unitary
open scoped Matrix

namespace KleinData

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinData F K σ₀ b c)

theorem Xmat_eVec_zero : D.Xmat (eVec 3 iZ) = skew6 1 0 0 0 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, skew6, eVec, iZ, iO]

theorem Xmat_fVec_zero : D.Xmat (fVec 3 iZ) = skew6 0 1 0 0 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, skew6, fVec, iZ, iO]

theorem Xmat_eVec_one : D.Xmat (eVec 3 iO) = skew6 0 0 D.δ 0 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, skew6, eVec, iZ, iO]

theorem Xmat_fVec_one : D.Xmat (fVec 3 iO) = skew6 0 0 0 (-D.ε) 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, skew6, fVec, iZ, iO]

theorem Xmat_planeVec (p : Fin 2 → F) : D.Xmat (planeVec 3 p) =
    skew6 0 0 0 0 (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω)
      (algebraMap F K (p 0) + algebraMap F K (p 1) * algebraMap F K b +
        algebraMap F K (p 1) * D.ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, skew6, planeVec]

theorem long_e0f1 (x : F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + x • (D.Xmat (eVec 3 iZ) * D.Hs (D.Xmat (fVec 3 iO))) =
      longRootMatrix (1 : Fin 4) (algebraMap F K x * D.ε) := by
  rw [← algebraMap_smul K x, Xmat_eVec_zero, Xmat_fVec_one, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew6, longRootMatrix, D.σ_ε, Fin.rev]
  all_goals simp [Algebra.smul_def]

theorem long_e1f0 (x : F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + x • (D.Xmat (eVec 3 iO) * D.Hs (D.Xmat (fVec 3 iZ))) =
      longRootMatrix (2 : Fin 4) (algebraMap F K x * D.δ) := by
  rw [← algebraMap_smul K x, Xmat_eVec_one, Xmat_fVec_zero, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew6, longRootMatrix, Fin.rev]
  all_goals simp [Algebra.smul_def]

theorem long_e0e1 (x : F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + x • (D.Xmat (eVec 3 iZ) * D.Hs (D.Xmat (eVec 3 iO))) =
      longRootMatrix (0 : Fin 4) (algebraMap F K x * D.δ) := by
  rw [← algebraMap_smul K x, Xmat_eVec_zero, Xmat_eVec_one, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew6, longRootMatrix, D.σ_δ, Fin.rev]
  all_goals simp [Algebra.smul_def]

theorem long_f0f1 (x : F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + x • (D.Xmat (fVec 3 iZ) * D.Hs (D.Xmat (fVec 3 iO))) =
      longRootMatrix (3 : Fin 4) (-(algebraMap F K x * D.ε)) := by
  rw [← algebraMap_smul K x, Xmat_fVec_zero, Xmat_fVec_one, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew6, longRootMatrix, D.σ_ε, Fin.rev]
  all_goals simp [Algebra.smul_def]


theorem short_e1 (p : Fin 2 → F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + D.Xmat (planeVec 3 p) * D.Hs (D.Xmat (eVec 3 iO)) =
      rootMatrix σ₀ (0 : Fin 4) 1
        (-(D.δ * (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω))) := by
  rw [Xmat_planeVec, Xmat_eVec_one, Hs_skew6, D.σ_δ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew6, rootMatrix, D.σ_δ, D.σ_sub_mul, Fin.rev] <;> ring

theorem short_f1 (p : Fin 2 → F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + D.Xmat (planeVec 3 p) * D.Hs (D.Xmat (fVec 3 iO)) =
      rootMatrix σ₀ (1 : Fin 4) 0
        (D.ε * (algebraMap F K (p 0) + algebraMap F K (p 1) * algebraMap F K b +
          algebraMap F K (p 1) * D.ω)) := by
  rw [Xmat_planeVec, Xmat_fVec_one, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew6, rootMatrix, D.σ_ε, D.σ_add_mul, Fin.rev] <;> ring

theorem short_e0 (p : Fin 2 → F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + D.Xmat (planeVec 3 p) * D.Hs (D.Xmat (eVec 3 iZ)) =
      rootMatrix σ₀ (0 : Fin 4) 2 (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω) := by
  rw [Xmat_planeVec, Xmat_eVec_zero, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew6, rootMatrix, D.σ_sub_mul, Fin.rev]

theorem short_f0 (p : Fin 2 → F) :
    (1 : Matrix (Fin 4) (Fin 4) K) + D.Xmat (planeVec 3 p) * D.Hs (D.Xmat (fVec 3 iZ)) =
      rootMatrix σ₀ (3 : Fin 4) 1 (algebraMap F K (p 0) - algebraMap F K (p 1) * D.ω) := by
  rw [Xmat_planeVec, Xmat_fVec_zero, Hs_skew6]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew6, rootMatrix, D.σ_sub_mul, Fin.rev]

end KleinData

end CFSG.ClassicalInvolution.WeakCT.SU4
