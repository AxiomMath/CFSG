module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.D4

open Matrix CFSG CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O

variable {K : Type} [Field K]

abbrev hypJ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K := fromBlocks 0 1 1 0

theorem dot_hypJ (u : Fin 4 ⊕ Fin 4 → K) :
    u ⬝ᵥ hypJ *ᵥ u = 2 * ∑ i, u (Sum.inl i) * u (Sum.inr i) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero, Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [two_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

abbrev gramCoord : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K :=
  Matrix.reindex (plusIndexEquiv 4) (plusIndexEquiv 4) ((2 : K)⁻¹ • hypJ)

theorem gramCoord_transpose : (gramCoord : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = gramCoord := by
  rw [gramCoord, transpose_reindex, transpose_smul, fromBlocks_transpose]
  simp

theorem dot_gramCoord (h2 : (2 : K) ≠ 0) (v : Fin (2 * 4) → K) :
    v ⬝ᵥ (gramCoord : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = coordinateQuadPlus 4 K v := by
  rw [gramCoord, reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm,
    dotProduct_comp_equiv_symm, smul_mulVec, dotProduct_smul, smul_eq_mul, dot_hypJ,
    coordinateQuadPlus, reindexQuadraticForm_apply, coe_quadPlus, StatedQuadPlus]
  field_simp
  rfl

theorem hypJ_conj :
    (fromBlocks 1 1 1 (-1) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)ᵀ * hypJ *
        fromBlocks 1 1 1 (-1) = fromBlocks ((2 : K) • 1) 0 0 ((-2 : K) • 1) := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [transpose_one, transpose_neg, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg]
  congr 1 <;> module

theorem isSquare_det_hypJ (h2 : (2 : K) ≠ 0) :
    IsSquare (hypJ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).det := by
  have e := congrArg det (hypJ_conj (K := K))
  rw [det_mul, det_mul, det_transpose, det_fromBlocks_zero₂₁, det_smul, det_smul, det_one] at e
  simp only [Fintype.card_fin, mul_one] at e
  set m := (fromBlocks 1 1 1 (-1) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).det with hm
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at e
    have : (2 : K) ^ 4 * (-2) ^ 4 ≠ 0 := by
      apply mul_ne_zero <;> exact pow_ne_zero _ (by simpa using h2)
    exact this e.symm
  refine ⟨(2 : K) ^ 4 / m, ?_⟩
  field_simp
  linear_combination e

theorem isSquare_det_gram_coord (h2 : (2 : K) ≠ 0) {R : GL (Fin (2 * 4)) K}
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R)
    (hRQ : ∀ v, oQ R v = coordinateQuadPlus 4 K v) :
    IsSquare (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).det := by
  have hRe : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = gramCoord :=
    eq_of_forall_dotProduct_mulVec h2 hR gramCoord_transpose fun v => by
      rw [← oQ_apply, hRQ, dot_gramCoord h2]
  rw [hRe, gramCoord, det_reindex_self, det_smul]
  obtain ⟨r, hr⟩ := isSquare_det_hypJ h2
  refine ⟨((2 : K)⁻¹) ^ 4 * r, ?_⟩
  rw [hr]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

end CFSG.ComponentClassification.Burgoyne.D4
