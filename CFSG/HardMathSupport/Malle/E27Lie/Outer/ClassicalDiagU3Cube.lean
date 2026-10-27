module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU3Block

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {ℓ f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

theorem scalar_mul_mem_gramSU (y : primeFormUnitary h (idGram F 3)) (b : F) (hb : b ≠ 0)
    (hN : h.norm b = 1) (hdet : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = b ^ 3) :
    GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b⁻¹ (inv_ne_zero hb)) * (y : GL (Fin 3) F) ∈
      gramSU h (idGram F 3) := by
  have hm : ((GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b⁻¹ (inv_ne_zero hb)) *
      (y : GL (Fin 3) F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      b⁻¹ • ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hy := mem_primeFormUnitary.mp y.2
  have hbb : h.bar b⁻¹ * b⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, mul_comm]
    have : b * h.bar b = 1 := hN
    rw [this, inv_one]
  refine ⟨?_, ?_⟩
  · rw [hm, Matrix.map_smul' _ _ _ (map_mul h.bar), Matrix.transpose_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm b⁻¹, hbb, one_smul]
    exact hy
  · rw [hm, Matrix.det_smul, hdet]
    simp [inv_mul_cancel₀ (pow_ne_zero 3 hb)]

theorem primeFormConjHom_inner_of_cube [Finite F] (hg : 3 ∣ ℓ ^ f + 1)
    (y : primeFormUnitary h (idGram F 3)) (c : Fˣ)
    (hdet : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = c) (b : F) (hb : b ^ 3 = c) :
    ∃ k : primeFormP h (idGram F 3), primeFormConjHom h (idGram F 3) y = MulAut.conj k := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hb]; norm_num)
  have hdetb : ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = b ^ 3 := by rw [hdet, hb]
  have hNc : h.norm (b ^ 3) = 1 := by rw [← hdetb]; exact norm_det_eq_one y
  have hNb := norm_eq_one_of_norm_cube_eq_one hg b hb0 hNc
  set S : GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3) (Units.mk0 b⁻¹ (inv_ne_zero hb0))
    with hS
  have hmem := scalar_mul_mem_gramSU y b hb0 hNb hdetb
  refine ⟨((⟨S * (y : GL (Fin 3) F), hmem⟩ : gramSU h (idGram F 3)) : primeFormP h (idGram F 3)),
    MulEquiv.ext fun x => QuotientGroup.induction_on x fun t => ?_⟩
  rw [primeFormConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  change (y : GL (Fin 3) F) * (t : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹ =
    S * (y : GL (Fin 3) F) * (t : GL (Fin 3) F) * (S * (y : GL (Fin 3) F))⁻¹
  calc (y : GL (Fin 3) F) * (t : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹
      = ((y : GL (Fin 3) F) * (t : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹) * S * S⁻¹ := by group
    _ = S * ((y : GL (Fin 3) F) * (t : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹) * S⁻¹ := by
      rw [(commute_scalar (Units.mk0 b⁻¹ (inv_ne_zero hb0))
        ((y : GL (Fin 3) F) * (t : GL (Fin 3) F) * (y : GL (Fin 3) F)⁻¹)).eq]
    _ = _ := by group

end CFSG.HardMathSupport.Malle.E27Lie
