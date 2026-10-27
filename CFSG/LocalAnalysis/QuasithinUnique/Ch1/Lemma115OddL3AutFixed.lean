module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open scoped MatrixGroups

section Fixed

variable {F : Type} [Field F]

@[expose] def soForm (R : Matrix (Fin 3) (Fin 3) F) : Subgroup SL(3, F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (g : Matrix (Fin 3) (Fin 3) F) = R}
  mul_mem' {g h} hg hh := by
    change ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * R *
      ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = R
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]
    calc ((h : Matrix (Fin 3) (Fin 3) F)ᵀ * (g : Matrix (Fin 3) (Fin 3) F)ᵀ) * R *
          ((g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F))
        = (h : Matrix (Fin 3) (Fin 3) F)ᵀ * ((g : Matrix (Fin 3) (Fin 3) F)ᵀ * R *
            (g : Matrix (Fin 3) (Fin 3) F)) * (h : Matrix (Fin 3) (Fin 3) F) := by
          simp only [Matrix.mul_assoc]
      _ = R := by
          change (g : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (g : Matrix (Fin 3) (Fin 3) F) = R at hg
          change (h : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (h : Matrix (Fin 3) (Fin 3) F) = R at hh
          rw [hg, hh]
  one_mem' := by
    change ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * R *
      ((1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = R
    simp
  inv_mem' {g} hg := by
    change ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * R *
      ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = R
    change (g : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (g : Matrix (Fin 3) (Fin 3) F) = R at hg
    have hgg : (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * R *
          ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
        = ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ *
            ((g : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (g : Matrix (Fin 3) (Fin 3) F)) *
            ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by rw [hg]
      _ = ((g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))ᵀ * R *
            ((g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = R := by rw [hgg]; simp

@[expose] noncomputable def soProj (R : Matrix (Fin 3) (Fin 3) F) :
    soForm R →* projectiveSL 3 F :=
  (proj 3 F).comp (soForm R).subtype

theorem scalar_transpose_mul_mul (R : Matrix (Fin 3) (Fin 3) F) (c : F) :
    (scalar (Fin 3) c)ᵀ * R * scalar (Fin 3) c = (c * c) • R := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
    smul_smul]

theorem soProj_injective {R : Matrix (Fin 3) (Fin 3) F} (hR : R ≠ 0) :
    Function.Injective (soProj R) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : proj 3 F (g : SL(3, F)) = 1 := hg
  obtain ⟨c, hc3, hcm⟩ := proj_eq_one_iff.1 hg'
  have hgR : (g : Matrix (Fin 3) (Fin 3) F)ᵀ * R * (g : Matrix (Fin 3) (Fin 3) F) = R := g.2
  rw [hcm, scalar_transpose_mul_mul] at hgR
  obtain ⟨i, j, hij⟩ : ∃ i j, R i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hR (Matrix.ext fun i j => hcon i j)
  have hcc : (c : F) * c = 1 := by
    have := congrFun (congrFun hgR i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hij (by rw [this, one_mul])
  have hc3' : (c : F) ^ 3 = 1 := by
    have := congrArg Units.val hc3
    simpa using this
  have hc1 : (c : F) = 1 := by
    calc (c : F) = (c : F) * ((c : F) * c) := by rw [hcc, mul_one]
      _ = (c : F) ^ 3 := by ring
      _ = 1 := hc3'
  refine Subtype.ext (Subtype.ext ?_)
  rw [hcm, hc1]
  simp

theorem exists_mem_soForm_of_fixed (A : GL (Fin 3) F) {x : projectiveSL 3 F}
    (hx : (conjAut 3 F A * dualAut 3 F) x = x) :
    ∃ y : soForm ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), soProj _ y = x := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at hx
  obtain ⟨c, hc3, hcm⟩ := proj_eq_proj_iff.1 hx
  set H : SL(3, F) := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A (g⁻¹).transpose
    with hH
  set G : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F) with hG
  set Gi : Matrix (Fin 3) (Fin 3) F := ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hGi
  set R : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hR
  have hGiG : Gi * G = 1 := by
    rw [hGi, hG, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hRA : R * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [hR, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hHm : (H : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) * Giᵀ * R :=
    coe_slConjugation A _
  have hHH : (H : Matrix (Fin 3) (Fin 3) F) * ((H⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcm' : ((H⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * G = scalar (Fin 3) (c : F) := by
    rw [hG, ← Matrix.SpecialLinearGroup.coe_mul]
    exact hcm
  have hGH : G = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * Giᵀ * R) := by
    calc G = ((H : Matrix (Fin 3) (Fin 3) F) * ((H⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) * G := by
          rw [hHH, Matrix.one_mul]
      _ = (H : Matrix (Fin 3) (Fin 3) F) *
            (((H⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * G) := by rw [Matrix.mul_assoc]
      _ = (H : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (c : F) := by rw [hcm']
      _ = (c : F) • (H : Matrix (Fin 3) (Fin 3) F) := by
          rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
      _ = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * Giᵀ * R) := by rw [hHm]
  have hRG : R * G = (c : F) • (Giᵀ * R) := by
    calc R * G = R * ((c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * Giᵀ * R)) := by rw [← hGH]
      _ = (c : F) • (R * (A : Matrix (Fin 3) (Fin 3) F) * Giᵀ * R) := by
          rw [Matrix.mul_smul]
          simp only [Matrix.mul_assoc]
      _ = (c : F) • (Giᵀ * R) := by rw [hRA, Matrix.one_mul]
  have hGRG : Gᵀ * R * G = (c : F) • R := by
    calc Gᵀ * R * G = Gᵀ * (R * G) := by rw [Matrix.mul_assoc]
      _ = Gᵀ * ((c : F) • (Giᵀ * R)) := by rw [hRG]
      _ = (c : F) • ((Gi * G)ᵀ * R) := by
          rw [Matrix.mul_smul, Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = (c : F) • R := by rw [hGiG, Matrix.transpose_one, Matrix.one_mul]
  have hc3' : (c : F) * ((c : F) * (c : F)) = 1 := by
    have := congrArg Units.val hc3
    simpa [pow_succ, mul_assoc] using this
  refine ⟨⟨scalarElement c hc3 * g, ?_⟩, ?_⟩
  · change ((scalarElement c hc3 * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)ᵀ * R *
      ((scalarElement c hc3 * g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = R
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Matrix.transpose_mul]
    calc (Gᵀ * (scalar (Fin 3) (c : F))ᵀ) * R * (scalar (Fin 3) (c : F) * G)
        = Gᵀ * ((scalar (Fin 3) (c : F))ᵀ * R * scalar (Fin 3) (c : F)) * G := by
          simp only [Matrix.mul_assoc]
      _ = R := by
          rw [scalar_transpose_mul_mul, Matrix.mul_smul, Matrix.smul_mul, hGRG, smul_smul]
          have h3 : (c : F) * c * c = 1 := by rw [mul_assoc]; exact hc3'
          rw [h3, one_smul]
  · change proj 3 F (scalarElement c hc3 * g) = proj 3 F g
    rw [map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hc3), one_mul]

end Fixed

end CFSG.QuasithinUnique.Ch1
