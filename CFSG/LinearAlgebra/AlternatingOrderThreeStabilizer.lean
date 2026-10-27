module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolBlock
public import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityPureGraphForms

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LinearAlgebra

open Matrix
open CFSG.ClassicalGroups.Alternating
open scoped Matrix

theorem exists_order_three_congr_fix_of_ne_zero
    {n : ℕ} {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hAt : Aᵀ = A) (hAdiag : ∀ i, A i i = 0) (hA : A ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      orderOf g = 3 ∧
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * A *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = A := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra h
    apply hA
    ext i j
    exact not_not.mp (not_exists.mp ((not_exists.mp h) i) j)
  let B : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) := Matrix.toBilin' A
  have hB : B.IsAlt := fun x => by
    change Matrix.toBilin' A x x = 0
    rw [Matrix.toBilin'_apply']
    exact CFSG.ComponentClassification.UnbalancedCatalog.dotProduct_mulVec_self_eq_zero
      hAt hAdiag x
  let a : Fin n → ZMod 2 := Pi.single i 1
  let b : Fin n → ZMod 2 := Pi.single j 1
  have hab : B a b ≠ 0 := by
    change Matrix.toBilin' A (Pi.single i 1) (Pi.single j 1) ≠ 0
    rw [Matrix.toBilin'_single]
    exact hij
  let T : Gsp B := Tsp hB a (B a b)⁻¹ * Tsp hB b (B a b)⁻¹
  have hT : orderOf T = 3 := orderOf_Tsp_mul_Tsp hB hab
  let Q : Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    Matrix.GeneralLinearGroup.toLin.symm
      (T : LinearMap.GeneralLinearGroup (ZMod 2) (Fin n → ZMod 2))
  have hQT : Matrix.GeneralLinearGroup.toLin Q =
      (T : LinearMap.GeneralLinearGroup (ZMod 2) (Fin n → ZMod 2)) :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)).apply_symm_apply _
  have hQ : orderOf Q = 3 := by
    calc orderOf Q = orderOf (Matrix.GeneralLinearGroup.toLin Q) :=
          ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := ZMod 2)).orderOf_eq Q).symm
      _ = orderOf ((T : LinearMap.GeneralLinearGroup (ZMod 2)
            (Fin n → ZMod 2))) := by rw [hQT]
      _ = orderOf T := Subgroup.orderOf_coe T
      _ = 3 := hT
  have happ : ∀ x : Fin n → ZMod 2, T.app x = Q *ᵥ x := by
    intro x
    change ((T : LinearMap.GeneralLinearGroup (ZMod 2) (Fin n → ZMod 2)) :
      (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) x = Q *ᵥ x
    rw [← hQT, Matrix.GeneralLinearGroup.coe_toLin]
    rfl
  have hform : ∀ x y : Fin n → ZMod 2, B (Q *ᵥ x) (Q *ᵥ y) = B x y := by
    intro x y
    rw [← happ x, ← happ y]
    exact T.2 x y
  have hmat : (Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * A *
      (Q : Matrix (Fin n) (Fin n) (ZMod 2)) = A := by
    refine (Matrix.toBilin' (n := Fin n) (R₁ := ZMod 2)).injective ?_
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    calc x ⬝ᵥ ((((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * A *
          (Q : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ y))
        = x ⬝ᵥ ((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
            (A *ᵥ ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y))) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) ⬝ᵥ
            (A *ᵥ ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y)) := by
          rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
      _ = B ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
            ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y) := by
          rw [Matrix.toBilin'_apply']
      _ = B x y := hform x y
      _ = x ⬝ᵥ (A *ᵥ y) := by rw [Matrix.toBilin'_apply']
  have hdet : IsUnit ((Q : Matrix (Fin n) (Fin n) (ZMod 2)).det) :=
    Matrix.isUnits_det_units Q
  have hQinv : ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = (Q : Matrix (Fin n) (Fin n) (ZMod 2))⁻¹ :=
    Matrix.GeneralLinearGroup.coe_inv Q
  have hfix : ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * A *
      ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = A := by
    rw [hQinv, Matrix.transpose_nonsing_inv]
    have hdetT : IsUnit (((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ).det) := by
      rwa [Matrix.det_transpose]
    calc ((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)⁻¹ * A *
          (Q : Matrix (Fin n) (Fin n) (ZMod 2))⁻¹
        = ((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)⁻¹ *
            ((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ * A *
              (Q : Matrix (Fin n) (Fin n) (ZMod 2))) *
            (Q : Matrix (Fin n) (Fin n) (ZMod 2))⁻¹ := by rw [hmat]
      _ = (((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)⁻¹ *
            (Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) * A *
            ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (Q : Matrix (Fin n) (Fin n) (ZMod 2))⁻¹) := by noncomm_ring
      _ = A := by
          rw [Matrix.nonsing_inv_mul ((Q : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) hdetT,
            Matrix.mul_nonsing_inv (Q : Matrix (Fin n) (Fin n) (ZMod 2)) hdet,
            Matrix.one_mul, Matrix.mul_one]
  obtain ⟨g, hg⟩ := CFSG.GroupTheory.GLnTwoSplitting.toGL_surjective_zmod_two
    (Matrix.GeneralLinearGroup.inverseTranspose Q)
  refine ⟨g, ?_, ?_⟩
  · have horder := orderOf_injective
      (Matrix.SpecialLinearGroup.toGL (n := Fin n) (R := ZMod 2))
      Matrix.SpecialLinearGroup.toGL_injective g
    rw [← horder, hg, MulEquiv.orderOf_eq]
    exact hQ
  · have hgmat : (g : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((Q⁻¹ : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
      rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix g, hg,
        Matrix.GeneralLinearGroup.coe_inverseTranspose]
    rw [hgmat, Matrix.transpose_transpose]
    exact hfix

end CFSG.LinearAlgebra
