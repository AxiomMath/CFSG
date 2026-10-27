module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Lifted
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL)

section Mat

variable {F : Type} [Field F]

theorem ii4_commute_of_slConjugation_fix (G : GL (Fin 2) F) (c : SpecialLinearGroup (Fin 2) F)
    (h : slConjugation F G c = c) : (G : Matrix (Fin 2) (Fin 2) F) * c = c * G := by
  have h2 := congrArg SpecialLinearGroup.toGL h
  rw [slConjugation_toGL] at h2
  have h3 : G * SpecialLinearGroup.toGL c = SpecialLinearGroup.toGL c * G := by
    calc G * SpecialLinearGroup.toGL c = (G * SpecialLinearGroup.toGL c * G⁻¹) * G := by group
      _ = SpecialLinearGroup.toGL c * G := by rw [h2]
  have h4 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
  simpa using h4

theorem ii4_sq_scalar_of_slConjugation_sq (G : GL (Fin 2) F)
    (h : slConjugation F G * slConjugation F G = 1) :
    ∃ μ : F, (G : Matrix (Fin 2) (Fin 2) F) * G = μ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hcomm : ∀ X : SpecialLinearGroup (Fin 2) F,
      ((G : Matrix (Fin 2) (Fin 2) F) * G) * X = X * ((G : Matrix (Fin 2) (Fin 2) F) * G) := by
    intro X
    have h1 := congrArg (fun α : MulAut (SpecialLinearGroup (Fin 2) F) => α X) h
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    have h2 := congrArg SpecialLinearGroup.toGL h1
    rw [slConjugation_toGL, slConjugation_toGL] at h2
    have h3 : G * G * SpecialLinearGroup.toGL X = SpecialLinearGroup.toGL X * (G * G) := by
      calc G * G * SpecialLinearGroup.toGL X
          = (G * (G * SpecialLinearGroup.toGL X * G⁻¹) * G⁻¹) * (G * G) := by group
        _ = SpecialLinearGroup.toGL X * (G * G) := by rw [h2]
    have h4 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simpa using h4
  let u : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let v : SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  exact exists_smul_one_of_commute_uv _ (hcomm u) (hcomm v)

theorem ii4_mat_sq_of_mem_center {c : SpecialLinearGroup (Fin 2) F}
    (hc : c * c ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    ∃ r : F, (c : Matrix (Fin 2) (Fin 2) F) * c = r • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  refine ⟨r, ?_⟩
  rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply, hr, Matrix.SpecialLinearGroup.coe_mul]

theorem ii4_det_sq_of_commute (h2 : (2 : F) ≠ 0)
    (A M : Matrix (Fin 2) (Fin 2) F) (hA : ∀ r : F, A ≠ r • (1 : Matrix (Fin 2) (Fin 2) F))
    (hdet : A.det = 1) (r : F) (hAA : A * A = r • (1 : Matrix (Fin 2) (Fin 2) F))
    (hM : M * A = A * M) (μ : F) (hMM : M * M = μ • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ t : F, M.det = t * t := by
  obtain ⟨x, y, hxy⟩ := exists_eq_smul_add_of_commute A hA M hM
  have hsq : M * M = (x * x + y * y * r) • (1 : Matrix (Fin 2) (Fin 2) F) + (2 * x * y) • A := by
    rw [hxy]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      smul_smul, hAA]
    module
  have h2xy : 2 * x * y = 0 := by
    by_contra hne
    apply hA ((μ - (x * x + y * y * r)) / (2 * x * y))
    have e : (2 * x * y) • A = (μ - (x * x + y * y * r)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      have h := hMM.symm.trans hsq
      calc (2 * x * y) • A = μ • (1 : Matrix (Fin 2) (Fin 2) F) -
          (x * x + y * y * r) • (1 : Matrix (Fin 2) (Fin 2) F) := by
            rw [h]; abel
        _ = (μ - (x * x + y * y * r)) • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [sub_smul]
    calc A = (2 * x * y)⁻¹ • ((2 * x * y) • A) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (2 * x * y)⁻¹ • ((μ - (x * x + y * y * r)) • (1 : Matrix (Fin 2) (Fin 2) F)) := by rw [e]
      _ = ((μ - (x * x + y * y * r)) / (2 * x * y)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [smul_smul, div_eq_inv_mul]
  have hxy0 : x = 0 ∨ y = 0 := by
    have : 2 * (x * y) = 0 := by linear_combination h2xy
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2
    · exact mul_eq_zero.1 h
  rcases hxy0 with rfl | rfl
  · refine ⟨y, ?_⟩
    rw [hxy]
    simp [hdet, sq]
  · refine ⟨x, ?_⟩
    rw [hxy]
    simp [sq]

theorem ii4_exists_conj_of_det_sq (G : GL (Fin 2) F) (t : F) (ht : t ≠ 0)
    (hdet : (G : Matrix (Fin 2) (Fin 2) F).det = t * t) :
    ∃ s : SpecialLinearGroup (Fin 2) F, slConjugation F G = MulAut.conj s := by
  obtain ⟨s, hs⟩ : ∃ s : SpecialLinearGroup (Fin 2) F,
      G = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht) * SpecialLinearGroup.toGL s := by
    refine ⟨⟨t⁻¹ • (G : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
    · rw [Matrix.det_smul, hdet]
      simp only [Fintype.card_fin]
      field_simp
    · apply Units.ext
      rw [Units.val_mul]
      simp only [GeneralLinearGroup.coe_scalar, Units.val_mk0]
      show (G : Matrix (Fin 2) (Fin 2) F) =
        (Matrix.scalar (Fin 2) t) * (t⁻¹ • (G : Matrix (Fin 2) (Fin 2) F))
      rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul, mul_inv_cancel₀ ht,
        one_smul]
  refine ⟨s, ?_⟩
  apply MulEquiv.ext
  intro X
  apply SpecialLinearGroup.toGL_injective
  rw [slConjugation_toGL, hs, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set z : GL (Fin 2) F := GeneralLinearGroup.scalar (Fin 2) (Units.mk0 t ht) with hz
  have hc : ∀ a : GL (Fin 2) F, z * a = a * z := fun a => GeneralLinearGroup.scalar_commute _ a
  calc z * SpecialLinearGroup.toGL s * SpecialLinearGroup.toGL X * (z * SpecialLinearGroup.toGL s)⁻¹
      = z * (SpecialLinearGroup.toGL s * SpecialLinearGroup.toGL X *
          (SpecialLinearGroup.toGL s)⁻¹) * z⁻¹ := by
        group
    _ = (SpecialLinearGroup.toGL s * SpecialLinearGroup.toGL X *
          (SpecialLinearGroup.toGL s)⁻¹) * z * z⁻¹ := by
        rw [hc]
    _ = SpecialLinearGroup.toGL s * SpecialLinearGroup.toGL X *
          (SpecialLinearGroup.toGL s)⁻¹ := by
        group

theorem ii4_inner_of_slConjugation_fix (h2 : (2 : F) ≠ 0)
    (G : GL (Fin 2) F) (hG2 : slConjugation F G * slConjugation F G = 1)
    (c : SpecialLinearGroup (Fin 2) F) (hc : c ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F))
    (hcc : c * c ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F))
    (hfix : slConjugation F G c = c) :
    ∃ s : SpecialLinearGroup (Fin 2) F, slConjugation F G = MulAut.conj s := by
  obtain ⟨r, hr⟩ := ii4_mat_sq_of_mem_center hcc
  obtain ⟨μ, hμ⟩ := ii4_sq_scalar_of_slConjugation_sq G hG2
  obtain ⟨t, ht⟩ := ii4_det_sq_of_commute h2 (c : Matrix (Fin 2) (Fin 2) F)
    (G : Matrix (Fin 2) (Fin 2) F) (nonscalar_of_not_mem_center c hc) c.det_coe r hr
    (ii4_commute_of_slConjugation_fix G c hfix) μ hμ
  have ht0 : t ≠ 0 := by
    intro h0
    apply GeneralLinearGroup.det_ne_zero G
    rw [ht, h0, mul_zero]
  exact ii4_exists_conj_of_det_sq G t ht0 ht

end Mat

end CFSG.GH74.GLS.Bg.Pu5
