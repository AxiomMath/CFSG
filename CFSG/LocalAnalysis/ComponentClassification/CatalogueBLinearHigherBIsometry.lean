module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormSimilitude
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalAssembly

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearHigherB

open Matrix
open LinearMap (BilinForm)

universe u

variable {n : ℕ} {K : Type u} [Field K]

abbrev matrixForm (R : GL (Fin n) K) : BilinForm K (Fin n → K) :=
  Matrix.toBilin' (R : Matrix (Fin n) (Fin n) K)

theorem matrixForm_apply (R : GL (Fin n) K) (x y : Fin n → K) :
    matrixForm R x y = x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ y :=
  Matrix.toBilin'_apply' _ _ _

theorem matrixForm_swap (R : GL (Fin n) K) (x y : Fin n → K) :
    matrixForm R y x = x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ y := by
  rw [matrixForm_apply, dotProduct_comm, ← vecMul_transpose, ← dotProduct_mulVec]

theorem isometryGroup_map_matrixForm (R : GL (Fin n) K) :
    (CatalogueBAlternatingIsometry.isometryGroup (matrixForm R)).map
        (CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun K (Fin n))).toMonoidHom =
      CatalogueBGraphForm.isometryGroup n K R := by
  ext g
  rw [Subgroup.mem_map_equiv,
    CatalogueBAlternatingIsometry.isometry_iff_matrix (Pi.basisFun K (Fin n)),
    MulEquiv.apply_symm_apply, CatalogueBGraphForm.mem_isometryGroup,
    LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']

@[expose] def isometryGroupEquiv (R : GL (Fin n) K) :
    CatalogueBAlternatingIsometry.isometryGroup (matrixForm R) ≃*
      CatalogueBGraphForm.isometryGroup n K R :=
  ((CatalogueBAlternatingIsometry.basisMatrixEquiv (Pi.basisFun K (Fin n))).subgroupMap
    _).trans (MulEquiv.subgroupCongr (isometryGroup_map_matrixForm R))

theorem matrixForm_nondegenerate (R : GL (Fin n) K) : (matrixForm R).Nondegenerate :=
  LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    (Matrix.isUnits_det_units R).ne_zero

theorem matrixForm_isAlt (hodd : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K)) :
    (matrixForm R).IsAlt := by
  intro x
  have hneg : matrixForm R x x = -matrixForm R x x := by
    conv_lhs => rw [matrixForm_swap, hR, neg_mulVec, dotProduct_neg]
    rw [matrixForm_apply]
  have htwo : (2 : K) * matrixForm R x x = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp htwo).resolve_left (Ring.two_ne_zero hodd)

theorem matrixForm_symm (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)) (x y : Fin n → K) :
    matrixForm R y x = matrixForm R x y := by
  rw [matrixForm_swap, hR, matrixForm_apply]

abbrev matrixQuadraticForm (R : GL (Fin n) K) : QuadraticForm K (Fin n → K) :=
  (matrixForm R).toQuadraticMap

theorem polarBilin_matrixQuadraticForm (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)) :
    (matrixQuadraticForm R).polarBilin =
      Matrix.toBilin' ((2 : K) • (R : Matrix (Fin n) (Fin n) K)) := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.flip_apply, matrixForm_symm R hR x y, map_smul, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul, two_mul]

theorem polarBilin_matrixQuadraticForm_nondegenerate (hodd : ringChar K ≠ 2)
    (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)) :
    (matrixQuadraticForm R).polarBilin.Nondegenerate := by
  rw [polarBilin_matrixQuadraticForm R hR]
  refine LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr ?_
  rw [det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Ring.two_ne_zero hodd)) (Matrix.isUnits_det_units R).ne_zero

theorem orthogonalGroup_matrixQuadraticForm (hodd : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)) :
    TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R) =
      CatalogueBAlternatingIsometry.isometryGroup (matrixForm R) := by
  have htwo : (2 : K) ≠ 0 := Ring.two_ne_zero hodd
  rw [TauCeti.QuadraticMap.orthogonalGroup_eq_isometryGroup_polarBilin
    (IsRegular.of_ne_zero htwo).isSMulRegular]
  ext g
  rw [TauCeti.BilinForm.mem_isometryGroup_iff,
    CatalogueBAlternatingIsometry.mem_isometryGroup_iff, polarBilin_matrixQuadraticForm R hR]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact forall₂_congr fun x y => mul_right_inj' htwo

theorem odd_card_of_ringChar_ne_two (K : Type u) [Field K] [Finite K] (hodd : ringChar K ≠ 2) :
    Odd (Nat.card K) := by
  let := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)

theorem alternating_isometry_pComponent_quasisimple [Finite K] (hodd : ringChar K ≠ 2)
    (hn : 4 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = -(R : Matrix (Fin n) (Fin n) K))
    (p : ℕ) (hp : p.Prime) (J : Subgroup (CatalogueBGraphForm.isometryGroup n K R))
    (hJ : CFSG.IsPComponent p J) : CFSG.IsQuasisimple J := by
  have hsymp := CatalogueBAlternatingIsometry.odd_symplectic_isometry_p_components (matrixForm R)
    (matrixForm_isAlt hodd R hR) (matrixForm_nondegenerate R)
    (by rwa [Module.finrank_fin_fun]) (odd_card_of_ringChar_ne_two K hodd)
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    (isometryGroupEquiv R).symm (fun L hL => (hsymp.2 p hp L hL).2) J hJ

theorem symmetric_isometry_pComponent_quasisimple [Finite K] (hodd : ringChar K ≠ 2)
    (hn : 3 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K))
    (p : ℕ) (hp : p.Prime) (J : Subgroup (CatalogueBGraphForm.isometryGroup n K R))
    (hJ : CFSG.IsPComponent p J) : CFSG.IsQuasisimple J := by
  have horth := CatalogueBOrthogonalAssembly.odd_orthogonal_p_components_assembly
    (odd_card_of_ringChar_ne_two K hodd)
    (matrixQuadraticForm R) (polarBilin_matrixQuadraticForm_nondegenerate hodd R hR)
    (by rwa [Module.finrank_fin_fun]) p hp
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p
    ((isometryGroupEquiv R).symm.trans
      (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd R hR).symm)) horth J hJ

end CFSG.ComponentClassification.CatalogueBLinearHigherB
