module

public import CFSG.ClassicalInvolution.Asc77.AscCX4L2

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

@[expose] def spForm (m n : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]

@[expose] def IsSim (M : Matrix (Fin 4) (Fin 4) F) (g : SL(4, F)) (c : F) : Prop :=
  (g : Matrix (Fin 4) (Fin 4) F) * M * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = c • M

theorem coe_inv_mul_self (g : SL(4, F)) :
    ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv_self (g : SL(4, F)) :
    (g : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem IsSim.one (M : Matrix (Fin 4) (Fin 4) F) : IsSim M 1 1 := by
  simp [IsSim]

theorem IsSim.mul {M : Matrix (Fin 4) (Fin 4) F} {g h : SL(4, F)} {c d : F} (hg : IsSim M g c)
    (hh : IsSim M h d) : IsSim M (g * h) (c * d) := by
  unfold IsSim at *
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
  calc (g : Matrix (Fin 4) (Fin 4) F) * (h : Matrix (Fin 4) (Fin 4) F) * M *
        ((h : Matrix (Fin 4) (Fin 4) F)ᵀ * (g : Matrix (Fin 4) (Fin 4) F)ᵀ)
      = (g : Matrix (Fin 4) (Fin 4) F) * ((h : Matrix (Fin 4) (Fin 4) F) * M *
          (h : Matrix (Fin 4) (Fin 4) F)ᵀ) * (g : Matrix (Fin 4) (Fin 4) F)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = (c * d) • M := by
        rw [hh, Matrix.mul_smul, Matrix.smul_mul, hg, smul_smul, mul_comm]

theorem IsSim.inv {M : Matrix (Fin 4) (Fin 4) F} {g : SL(4, F)} {c : F} (hc : c ≠ 0)
    (hg : IsSim M g c) : IsSim M g⁻¹ c⁻¹ := by
  unfold IsSim at *
  set X : Matrix (Fin 4) (Fin 4) F := ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) with hX
  set Y : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin 4) (Fin 4) F) with hY
  have hXY : X * Y = 1 := coe_inv_mul_self g
  have h1 : M = c • (X * M * Xᵀ) := by
    calc M = (X * Y) * M * (X * Y)ᵀ := by
          rw [hXY, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      _ = X * (Y * M * Yᵀ) * Xᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = c • (X * M * Xᵀ) := by rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  calc X * M * Xᵀ = c⁻¹ • (c • (X * M * Xᵀ)) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • M := by rw [← h1]

@[expose] def spM (M : Matrix (Fin 4) (Fin 4) F) : Subgroup SL(4, F) where
  carrier := {g | IsSim M g 1}
  one_mem' := IsSim.one M
  mul_mem' {g h} hg hh := by
    have := IsSim.mul hg hh
    rwa [one_mul] at this
  inv_mem' {g} hg := by
    have := IsSim.inv one_ne_zero hg
    rwa [inv_one] at this

@[expose] def simM (M : Matrix (Fin 4) (Fin 4) F) : Subgroup SL(4, F) where
  carrier := {g | ∃ c : F, c ≠ 0 ∧ IsSim M g c}
  one_mem' := ⟨1, one_ne_zero, IsSim.one M⟩
  mul_mem' {g h} := by
    rintro ⟨c, hc, hg⟩ ⟨d, hd, hh⟩
    exact ⟨c * d, mul_ne_zero hc hd, hg.mul hh⟩
  inv_mem' {g} := by
    rintro ⟨c, hc, hg⟩
    exact ⟨c⁻¹, inv_ne_zero hc, hg.inv hc⟩

theorem mem_spM {M : Matrix (Fin 4) (Fin 4) F} {g : SL(4, F)} :
    g ∈ spM M ↔ (g : Matrix (Fin 4) (Fin 4) F) * M * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = M := by
  show IsSim M g 1 ↔ _
  rw [IsSim, one_smul]

theorem commutator_simM_le_spM (M : Matrix (Fin 4) (Fin 4) F) :
    ⁅simM M, simM M⁆ ≤ spM M := by
  rw [Subgroup.commutator_le]
  rintro a ⟨c, hc, ha⟩ b ⟨d, hd, hb⟩
  have h := ((ha.mul hb).mul (ha.inv hc)).mul (hb.inv hd)
  have e : c * d * c⁻¹ * d⁻¹ = 1 := by field_simp
  rw [e] at h
  show IsSim M ⁅a, b⁆ 1
  rw [commutatorElement_def]
  exact h

theorem mem_simM_of_proj_eq (A : GL (Fin 4) F) {g : SL(4, F)}
    (h : proj 4 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
      ((g⁻¹).transpose)) = proj 4 F g) :
    g ∈ simM (A : Matrix (Fin 4) (Fin 4) F) := by
  rw [proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  set a := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
    ((g⁻¹).transpose) with ha
  have hga : (g : Matrix (Fin 4) (Fin 4) F) = (c : F) • (a : Matrix (Fin 4) (Fin 4) F) := by
    have e : g = a * (a⁻¹ * g) := by group
    rw [e, Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hAi : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcoe : (a : Matrix (Fin 4) (Fin 4) F) = (A : Matrix (Fin 4) (Fin 4) F) *
      (((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [ha, coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  refine ⟨c, c.ne_zero, ?_⟩
  show (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (c : F) • A
  calc (g : Matrix (Fin 4) (Fin 4) F) * A * (g : Matrix (Fin 4) (Fin 4) F)ᵀ =
        (c : F) • ((A : Matrix (Fin 4) (Fin 4) F) *
          (((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ *
            (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A) *
              (g : Matrix (Fin 4) (Fin 4) F)ᵀ) := by
        rw [hga, hcoe, Matrix.smul_mul, Matrix.smul_mul]
        simp only [Matrix.mul_assoc]
    _ = (c : F) • ((A : Matrix (Fin 4) (Fin 4) F) *
          ((g : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ) := by
        rw [hAi, Matrix.mul_one, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (c : F) • (A : Matrix (Fin 4) (Fin 4) F) := by
        rw [coe_mul_inv_self, Matrix.transpose_one, Matrix.mul_one]

theorem slConj_eq_of_mem_spM (A : GL (Fin 4) F) {g : SL(4, F)}
    (hg : g ∈ spM (A : Matrix (Fin 4) (Fin 4) F)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
      ((g⁻¹).transpose) = g :=
  CX.CX4.L4.conj_inv_transpose_of_symp A g (mem_spM.mp hg)

theorem block0_le_spM (m n : F) :
    (blockSL F 4 2 0 (by norm_num)).range ≤ spM (spForm m n) := by
  rintro _ ⟨b, rfl⟩
  rw [mem_spM, coe_blockSL, blockMat_four_zero]
  have hb := b.2
  rw [Matrix.det_fin_two] at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spForm, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination m * hb | linear_combination (-m) * hb

theorem block2_le_spM (m n : F) :
    (blockSL F 4 2 2 (by norm_num)).range ≤ spM (spForm m n) := by
  rintro _ ⟨b, rfl⟩
  rw [mem_spM, coe_blockSL, blockMat_four_two]
  have hb := b.2
  rw [Matrix.det_fin_two] at hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spForm, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    first | ring1 | linear_combination n * hb | linear_combination (-n) * hb

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
