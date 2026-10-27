module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphForm

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearHigherB

open Matrix CFSG.LocalAnalysis.ComponentInitial CatalogueBGraphForm

universe u

variable {n : ℕ} {K : Type u} [Field K]

theorem transpose_inv_of_transpose_eq (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = A) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = (A⁻¹ : GL (Fin n) K) := by
  have h : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      (A : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ
      = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          ((A : Matrix (Fin n) (Fin n) K) * (A⁻¹ : GL (Fin n) K)) := by
        rw [Units.mul_inv, Matrix.mul_one]
    _ = (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          (A : Matrix (Fin n) (Fin n) K)ᵀ) * (A⁻¹ : GL (Fin n) K) := by
        rw [hA, Matrix.mul_assoc]
    _ = (A⁻¹ : GL (Fin n) K) := by rw [h, Matrix.one_mul]

theorem transpose_inv_of_transpose_eq_neg (A : GL (Fin n) K)
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ = -(A : Matrix (Fin n) (Fin n) K)) :
    ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      -((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      (A : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  calc ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ
      = (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          (A : Matrix (Fin n) (Fin n) K)) * (A⁻¹ : GL (Fin n) K) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    _ = (-(((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
          (A : Matrix (Fin n) (Fin n) K)ᵀ)) * (A⁻¹ : GL (Fin n) K) := by
        rw [hA, Matrix.mul_neg, neg_neg]
    _ = -((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [h, Matrix.neg_mul, Matrix.one_mul]

theorem inverse_isometry_pComponent_quasisimple [Finite K] (hodd : ringChar K ≠ 2)
    (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hform : (A : Matrix (Fin n) (Fin n) K)ᵀ = A ∨
      ((A : Matrix (Fin n) (Fin n) K)ᵀ = -(A : Matrix (Fin n) (Fin n) K) ∧ Even n))
    (p : ℕ) (hp : p.Prime) (J : Subgroup (isometryGroup n K A⁻¹))
    (hJ : CFSG.IsPComponent p J) : CFSG.IsQuasisimple J := by
  rcases hform with hsymm | ⟨halt, heven⟩
  · exact symmetric_isometry_pComponent_quasisimple hodd hn A⁻¹
      (transpose_inv_of_transpose_eq A hsymm) p hp J hJ
  · have hn4 : 4 ≤ n := by
      obtain ⟨k, rfl⟩ := heven
      omega
    exact alternating_isometry_pComponent_quasisimple hodd hn4 A⁻¹
      (transpose_inv_of_transpose_eq_neg A halt) p hp J hJ

theorem pureGraph_fixed_pComponent_quasisimple [Finite K] (hodd : ringChar K ≠ 2) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (hne : pureGraphAction n K A ≠ 1) (hsq : pureGraphAction n K A ^ 2 = 1)
    (p : ℕ) (hp : p.Prime) (L : Subgroup (FixedCommutingProduct.fixedSubgroup
      (pureGraphAction n K A))) (hL : CFSG.IsPComponent p L) : CFSG.IsQuasisimple L := by
  obtain ⟨hform, hred⟩ := pure_graph_fixed_components_form_reduction n K hn hodd A hne hsq
  exact hred p hp (inverse_isometry_pComponent_quasisimple hodd hn A hform p hp) L hL

theorem odd_linear_pure_graph_involution_fixed_p_components (n : ℕ) (K : Type u) [Field K]
    [Finite K] (hodd : ringChar K ≠ 2) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hne : LinearFlag.conjAut n K A * LinearFlag.dualAut n K ≠ 1)
    (hsq : (LinearFlag.conjAut n K A * LinearFlag.dualAut n K) ^ 2 = 1) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup
        (LinearFlag.conjAut n K A * LinearFlag.dualAut n K)),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  intro p hp
  obtain ⟨hne', hsq'⟩ := congr_involution (nativeEquiv n K) hne hsq
  rw [congr_pureGraph] at hne' hsq'
  exact fixed_pComponent_quasisimple_of_congr (nativeEquiv n K) (congr_pureGraph A) p
    (pureGraph_fixed_pComponent_quasisimple hodd hn A hne' hsq' p hp)

end CFSG.ComponentClassification.CatalogueBLinearHigherB
