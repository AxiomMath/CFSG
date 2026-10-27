module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Matrix Subgroup FourGroupEvenCanonical
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenLinearSL.conjAut_mem_inner_of_sq_eq_one)

section Isometry

variable {k K : Type*} [Field k] [Field K] [CharP k 2] (φ : k →+* K) {n : ℕ}
  {Cl : Matrix (Fin n) (Fin n) k}

theorem det_map_eq_one_of_mem (hCl : Cl.det ≠ 0) {g : GL (Fin n) k}
    (hg : g ∈ matrixIsometryGroup Cl) : ((g : Matrix (Fin n) (Fin n) k).map φ).det = 1 := by
  rw [show (g : Matrix (Fin n) (Fin n) k).map φ = φ.mapMatrix (g : Matrix (Fin n) (Fin n) k) from
    rfl, ← RingHom.map_det, det_eq_one_of_mem hCl hg, map_one]

@[expose] def isometrySL (hCl : Cl.det ≠ 0) :
    matrixIsometryGroup Cl →* SpecialLinearGroup (Fin n) K where
  toFun g := ⟨((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map φ,
    det_map_eq_one_of_mem φ hCl g.2⟩
  map_one' := Subtype.ext (by
    change ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map φ = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero φ) (map_one φ)])
  map_mul' a b := Subtype.ext (by
    change (((a : GL (Fin n) k) * b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map φ =
      ((a : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map φ *
        ((b : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).map φ
    rw [Units.val_mul, Matrix.map_mul])

end Isometry

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag
