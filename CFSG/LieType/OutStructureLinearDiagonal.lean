module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGaussian

public section

namespace CFSG.LieType.OutStructure

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {K : Type*} [Field K]

@[expose] def diagonalFun (m : ℕ) (μ : K) (i : Fin m) : K :=
  if (i : ℕ) = 0 then μ else 1

@[expose] noncomputable def diagonalGL (m : ℕ) (μ : Kˣ) : GL (Fin m) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (diagonalFun m (μ : K))) (by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by
      by_cases h : (i : ℕ) = 0 <;> simp [diagonalFun, h]))

@[simp]
theorem coe_diagonalGL (m : ℕ) (μ : Kˣ) :
    (diagonalGL m μ : Matrix (Fin m) (Fin m) K) = Matrix.diagonal (diagonalFun m (μ : K)) := by
  simp [diagonalGL]

end CFSG.LieType.OutStructure
