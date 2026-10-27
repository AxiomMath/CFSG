module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUPair

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n m : ℕ}

theorem coe_adjInv_transvection {i j : Fin m} (hij : i ≠ j) (t : K) :
    (adjInv h (Matrix.SpecialLinearGroup.toGL
      (⟨transvection i j t, det_transvection_of_ne i j hij t⟩ :
        Matrix.SpecialLinearGroup (Fin m) K)) : Matrix (Fin m) (Fin m) K) =
      transvection j i (-h.bar t) := by
  set T : Matrix.SpecialLinearGroup (Fin m) K :=
    ⟨transvection i j t, det_transvection_of_ne i j hij t⟩
  set T' : Matrix.SpecialLinearGroup (Fin m) K :=
    ⟨transvection i j (-t), det_transvection_of_ne i j hij (-t)⟩
  have hTT : T * T' = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    change transvection i j t * transvection i j (-t) = 1
    rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero])
  have hinv : (Matrix.SpecialLinearGroup.toGL T)⁻¹ = Matrix.SpecialLinearGroup.toGL T' := by
    rw [← map_inv, inv_eq_of_mul_eq_one_right hTT]
  rw [coe_adjInv, hinv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  change ((transvection i j (-t)).map h.bar)ᵀ = transvection j i (-h.bar t)
  rw [transvection, transvection, Matrix.map_add _ (map_add h.bar),
    Matrix.map_one _ (map_zero h.bar) (map_one h.bar), map_single, transpose_add, transpose_one,
    transpose_single, map_neg]

section emb

variable (β : (Fin n → K) ≃ₗ[K] ((Fin m → K) × (Fin m → K)))
  (hF : ∀ v w, gramForm h 1 v w = gramForm h 1 (β v).1 (β w).2 + gramForm h 1 (β v).2 (β w).1)

include hF in
theorem blockConj_adjInv_mem {y : GL (Fin m) K} (hy : (y : Matrix (Fin m) (Fin m) K).det = 1) :
    blockConj β (y, adjInv h y) ∈ gramSU h (idGram K n) :=
  blockConj_mem_gramSU β h (fun u u' => gramForm h 1 u.1 u'.2 + gramForm h 1 u.2 u'.1) hF _
    (fun u u' => by
      simp only [gramForm_one_mulVec_mulVec, conjTranspose_mul_adjInv,
        conjTranspose_adjInv_mul, one_mulVec])
    (by rw [hy, det_adjInv h hy, one_mul])

@[expose] def pairEmb : Matrix.SpecialLinearGroup (Fin m) K →* gramSU h (idGram K n) :=
  (((blockConj β).comp ((MonoidHom.id _).prod (adjInv h))).comp
    Matrix.SpecialLinearGroup.toGL).codRestrict _ fun y =>
      blockConj_adjInv_mem h β hF (y := Matrix.SpecialLinearGroup.toGL y) y.2

theorem coe_pairEmb (y : Matrix.SpecialLinearGroup (Fin m) K) :
    (pairEmb h β hF y : GL (Fin n) K) = blockConj β (Matrix.SpecialLinearGroup.toGL y,
      adjInv h (Matrix.SpecialLinearGroup.toGL y)) := rfl

theorem pairEmb_injective : Function.Injective (pairEmb h β hF) := fun _ _ hyy =>
  Matrix.SpecialLinearGroup.toGL_injective
    (congrArg Prod.fst (blockConj_injective β (congrArg Subtype.val hyy)))

include hF in
theorem adjInv_of_isometry {y : GL (Fin m) K × GL (Fin m) K}
    (hy : blockConj β y ∈ gramSU h (idGram K n)) : y.2 = adjInv h y.1 := by
  have hiso : ∀ v w, gramForm h (1 : Matrix (Fin n) (Fin n) K)
      (((blockConj β y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (((blockConj β y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      gramForm h 1 v w := (mem_gramSU_iff_isometry.mp hy).1
  set M := ((y.1 : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ * (y.2 : Matrix (Fin m) (Fin m) K)
  have h1 : ∀ u u' : Fin m → K, gramForm h 1 u (M *ᵥ u') = gramForm h 1 u u' := by
    intro u u'
    have h2 := hiso (β.symm (u, 0)) (β.symm (0, u'))
    rw [hF, hF (β.symm (u, 0)), apply_blockConj_mulVec, apply_blockConj_mulVec,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2
    simp only [mulVec_zero, map_zero, add_zero] at h2
    rw [← gramForm_one_mulVec_mulVec, h2]
  have hM : M = 1 := by
    refine Matrix.ext_iff_mulVec.mpr fun u' => ?_
    rw [one_mulVec]
    funext i
    have h3 := h1 (Pi.single i 1) u'
    simpa [gramForm_apply, dotProduct, Pi.single_apply] using h3
  have h4 := conjTranspose_mul_adjInv h y.1
  have h5 : (adjInv h y.1 : Matrix (Fin m) (Fin m) K) *
      ((y.1 : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ = 1 := mul_eq_one_comm.mp h4
  apply Units.ext
  calc (y.2 : Matrix (Fin m) (Fin m) K) =
      ((adjInv h y.1 : Matrix (Fin m) (Fin m) K) *
        ((y.1 : Matrix (Fin m) (Fin m) K).map h.bar)ᵀ) * (y.2 : Matrix (Fin m) (Fin m) K) := by
        rw [h5, Matrix.one_mul]
    _ = adjInv h y.1 := by rw [Matrix.mul_assoc, show ((y.1 : Matrix (Fin m) (Fin m) K).map
        h.bar)ᵀ * (y.2 : Matrix (Fin m) (Fin m) K) = M from rfl, hM, Matrix.mul_one]

end emb

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
