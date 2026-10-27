module

import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups

variable {F : Type u} [Field F]

theorem exists_char_two_gl_fixed_columns [CharP F 2]
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (h : SL(2, F)) (hh : h * sl2FieldAction sigma h = 1) :
    ∃ C : GL (Fin 2) F,
      (h : Matrix (Fin 2) (Fin 2) F) *
        sigma.toRingHom.mapMatrix (C : Matrix (Fin 2) (Fin 2) F) = C := by
  classical
  let T := semilinearInvolution h sigma hsigma hh
  obtain ⟨b, hb⟩ := exists_char_two_semilinear_fixed_basis sigma hsigma hne T
    (semilinearApply_involutive h sigma hsigma hh) (semilinearApply_smul h sigma)
  let L : LinearMap.GeneralLinearGroup F (Fin 2 → F) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun.symm
  let C : GL (Fin 2) F := Matrix.GeneralLinearGroup.toLin.symm L
  have hCcol (i j : Fin 2) : (C : Matrix (Fin 2) (Fin 2) F) i j = b j i := by
    let ej : Fin 2 → F := Pi.single j 1
    have hfun : Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) F) ej = b j := by
      calc
        Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) F) ej =
            (Matrix.GeneralLinearGroup.toLin C : (Fin 2 → F) → Fin 2 → F) ej := rfl
        _ = (L : (Fin 2 → F) → Fin 2 → F) ej := by
          rw [(Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := F)).apply_symm_apply]
        _ = b j := by simp [L, ej, LinearMap.GeneralLinearGroup.ofLinearEquiv]
    rw [Matrix.mulVec_single_one] at hfun
    exact congrFun hfun i
  refine ⟨C, ?_⟩
  ext i j
  have hfix := congrFun (hb j) i
  change Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) F)
    (fun k => sigma (b j k)) i = b j i at hfix
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, hCcol] using hfix

theorem exists_char_two_sl2_coboundary [CharP F 2]
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (h : SL(2, F)) (hh : h * sl2FieldAction sigma h = 1) :
    ∃ x : SL(2, F), h * sl2FieldAction sigma x = x := by
  classical
  obtain ⟨C, hC⟩ := exists_char_two_gl_fixed_columns sigma hsigma hne h hh
  let B : Matrix (Fin 2) (Fin 2) F := C
  let d : F := B.det
  have hd : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero C
  have hdfix : sigma d = d := by
    have hdets := congrArg Matrix.det hC
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul,
      ← sigma.toRingHom.map_det] at hdets
    exact hdets
  let X : Matrix (Fin 2) (Fin 2) F := B.updateCol 0 (d⁻¹ • fun i => B i 0)
  have hXdet : X.det = 1 := by
    dsimp [X]
    rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]
    exact inv_mul_cancel₀ hd
  have hXcol (j : Fin 2) :
      semilinearApply h sigma (fun i => X i j) = fun i => X i j := by
    have hBcol : semilinearApply h sigma (fun i => B i j) = fun i => B i j := by
      ext i
      exact congrFun (congrFun hC i) j
    by_cases hj : j = 0
    · subst j
      simp only [X, Matrix.updateCol_self]
      rw [semilinearApply_smul, map_inv₀, hdfix, hBcol]
    · simpa only [X, Matrix.updateCol_ne hj] using hBcol
  let x : SL(2, F) := ⟨X, hXdet⟩
  refine ⟨x, ?_⟩
  ext i j
  exact congrFun (hXcol j) i

theorem outer_involution_sl2_conjugate [CharP F 2]
    (a : Gamma F) (ha : orderOf a = 2) (houter : a ∉ linearKernel F) :
    ∃ x : SL(2, F), a = (SemidirectProduct.inl x : Gamma F) *
      SemidirectProduct.inr a.right * (SemidirectProduct.inl x)⁻¹ := by
  obtain ⟨hne, hsigma, hh⟩ := outer_involution_cocycle a ha houter
  obtain ⟨x, hx⟩ := exists_char_two_sl2_coboundary a.right hsigma hne a.left hh
  refine ⟨x, ?_⟩
  apply eq_mul_inv_iff_mul_eq.mpr
  apply SemidirectProduct.ext
  · simpa using hx
  · simp

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
