module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG

open MvPolynomial Matrix

namespace FrobeniusDeterminant.Core

@[expose] noncomputable def ofFun (G : Type*) [Fintype G] (x : G → ℂ) :
    MonoidAlgebra ℂ G :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).symm
    (Finsupp.equivFunOnFinite.symm x)

@[simp] theorem ofFun_coeff (G : Type*) [Fintype G]
    (x : G → ℂ) (g : G) : (ofFun G x).coeff g = x g := by
  simp [ofFun, MonoidAlgebra.coeffLinearEquiv_symm_apply]

@[expose] noncomputable def invPerm (G : Type*) [Group G] : Equiv.Perm G where
  toFun g := g⁻¹
  invFun g := g⁻¹
  left_inv := inv_inv
  right_inv := inv_inv

private theorem leftMulMatrix_apply (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (x : G → ℂ) (g h : G) :
    (Algebra.leftMulMatrix (MonoidAlgebra.basis G ℂ) (ofFun G x)) g h =
      x (g * h⁻¹) := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, MonoidAlgebra.basis_apply]
  change ((MonoidAlgebra.basis G ℂ).repr
    (ofFun G x * MonoidAlgebra.single h 1)) g = _
  change (ofFun G x * MonoidAlgebra.single h 1).coeff g = _
  rw [MonoidAlgebra.coeff_mul_single_apply, ofFun_coeff]
  simp

theorem eval_groupDeterminant (G : Type*) [Group G] [Fintype G]
    [DecidableEq G] (x : G → ℂ) :
    MvPolynomial.eval x
        (CFSG.FrobeniusDeterminant.groupDeterminant G) =
      (Equiv.Perm.sign (invPerm G) : ℂ) *
        Algebra.norm ℂ (ofFun G x) := by
  rw [CFSG.FrobeniusDeterminant.groupDeterminant]
  rw [RingHom.map_det]
  rw [Algebra.norm_eq_matrix_det (MonoidAlgebra.basis G ℂ)]
  rw [← Matrix.det_permute' (invPerm G)]
  congr 1
  ext g h
  simp only [Matrix.submatrix_apply, id_eq, invPerm]
  rw [leftMulMatrix_apply]
  simp [CFSG.FrobeniusDeterminant.groupMatrix]

end FrobeniusDeterminant.Core

end CFSG
