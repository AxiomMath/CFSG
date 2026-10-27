module

public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut

public section

open Subgroup Matrix CFSG
open CFSG.Semidihedral.MatrixCoverData (slConjugation slConjugation_toGL slConjugation_matrix)
open CFSG.GH74.GLS.IVK.Lifted
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local

section Aut

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem slConjugation_coe (G : GL (Fin 2) F) (M : SL(2, F)) :
    ((slConjugation F G M : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  slConjugation_matrix F G M

omit [Finite F] in
theorem slConjugation_eq_one_of_scalar (G : GL (Fin 2) F) (c : F)
    (hc : (G : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    slConjugation F G = 1 := by
  apply MulEquiv.ext
  intro b
  apply SpecialLinearGroup.toGL_injective
  rw [slConjugation_toGL]
  have hcm : G * SpecialLinearGroup.toGL b = SpecialLinearGroup.toGL b * G := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc]
    simp
  rw [hcm]
  group
  rfl

omit [Finite F] in
theorem exists_scalar_of_slConjugation_eq_one (H : GL (Fin 2) F) (h : slConjugation F H = 1) :
    ∃ c : F, (H : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hcomm : ∀ X : SL(2, F),
      (X : Matrix (Fin 2) (Fin 2) F) * (H : Matrix (Fin 2) (Fin 2) F) =
        (H : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) := by
    intro X
    have h1 : slConjugation F H X = X := by rw [h]; rfl
    have h2 := congrArg SpecialLinearGroup.toGL h1
    rw [slConjugation_toGL] at h2
    have h3 : H * SpecialLinearGroup.toGL X = SpecialLinearGroup.toGL X * H := by
      calc H * SpecialLinearGroup.toGL X = (H * SpecialLinearGroup.toGL X * H⁻¹) * H := by group
        _ = SpecialLinearGroup.toGL X * H := by rw [h2]
    have h4 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h3
    simpa using h4.symm
  let u : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let v : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  exact exists_smul_one_of_commute_uv (H : Matrix (Fin 2) (Fin 2) F) (hcomm u).symm (hcomm v).symm

omit [Finite F] in
theorem slConjugation_toGL_eq_conj (y : SL(2, F)) :
    slConjugation F (SpecialLinearGroup.toGL y) = MulAut.conj y := by
  apply MulEquiv.ext
  intro X
  apply SpecialLinearGroup.toGL_injective
  rw [slConjugation_toGL, MulAut.conj_apply, map_mul, map_mul, map_inv]

omit [Finite F] in
theorem exists_conj_eq_slConjugation_of_isSquare_det (G : GL (Fin 2) F)
    (hsq : IsSquare (Matrix.det (G : Matrix (Fin 2) (Fin 2) F))) :
    ∃ y : SL(2, F), slConjugation F G = MulAut.conj y := by
  obtain ⟨l, hl⟩ := hsq
  have hD : Matrix.det (G : Matrix (Fin 2) (Fin 2) F) ≠ 0 := (isUnits_det_units G).ne_zero
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hD (by rw [hl]; simp)
  let y : SL(2, F) := ⟨l⁻¹ • (G : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_smul, hl]
    simp only [Fintype.card_fin]
    field_simp⟩
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) :
      GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = l⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    simp [Matrix.smul_one_eq_diagonal]
  have hy : SpecialLinearGroup.toGL y =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * G := by
    apply Units.ext
    rw [Units.val_mul, hsc, Matrix.smul_mul, Matrix.one_mul]
    rfl
  refine ⟨y, ?_⟩
  rw [← slConjugation_toGL_eq_conj, hy, map_mul,
    slConjugation_eq_one_of_scalar _ l⁻¹ hsc, one_mul]

theorem sl2_aut_inner_of_prime {p f r : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h3 : 3 < p ^ f) (hr : r.Prime) (hr2 : r ≠ 2) (hrf : ¬ r ∣ f)
    (α : MulAut SL(2, F)) (hα : α ^ r = 1) : ∃ y : SL(2, F), α = MulAut.conj y := by
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h3' : 3 < Nat.card F := hF ▸ h3
  set σ := (gammaOf hodd h3' α).right
  have hσr : σ ^ r = 1 := by
    have hpow : ∀ n : ℕ, (gammaOf hodd h3' (α ^ n)).right = σ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, gammaOf_mul_right, ih, pow_succ]
    rw [← hpow r, hα, map_one]
    rfl
  have hσ1 : σ = 1 := by
    have hAut : Nat.card (F ≃+* F) = f :=
      CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F hp hF
    have h1 : orderOf σ ∣ r := orderOf_dvd_of_pow_eq_one hσr
    have h2 : orderOf σ ∣ f := hAut ▸ _root_.orderOf_dvd_natCard σ
    have hcop : Nat.Coprime r f := (Nat.Prime.coprime_iff_not_dvd hr).2 hrf
    have h12 := Nat.dvd_gcd h1 h2
    rw [hcop] at h12
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h12)
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3' α hσ1
  have hGr : slConjugation F (G ^ r) = 1 := by rw [map_pow, ← hG, hα]
  obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq_one (G ^ r) hGr
  obtain ⟨k, hk⟩ := hr.eq_two_or_odd'.resolve_left hr2
  have hdet : (Matrix.det (G : Matrix (Fin 2) (Fin 2) F)) ^ r = c ^ 2 := by
    have := congrArg Matrix.det hc
    rw [Units.val_pow_eq_pow_val, Matrix.det_pow, Matrix.det_smul, Matrix.det_one] at this
    simpa using this
  have hD : Matrix.det (G : Matrix (Fin 2) (Fin 2) F) ≠ 0 := (isUnits_det_units G).ne_zero
  have hsq : IsSquare (Matrix.det (G : Matrix (Fin 2) (Fin 2) F)) := by
    refine ⟨c / (Matrix.det (G : Matrix (Fin 2) (Fin 2) F)) ^ k, ?_⟩
    rw [hk] at hdet
    field_simp
    linear_combination hdet
  obtain ⟨y, hy⟩ := exists_conj_eq_slConjugation_of_isSquare_det G hsq
  exact ⟨y, hG.trans hy⟩

theorem sl2_aut_matrix_form_of_involution (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut SL(2, F)) (hα : α * α = 1) (hne : α ≠ 1)
    (hfix : ∀ a b : SL(2, F), α a = a → α b = b → a * b = b * a) :
    ∃ G : GL (Fin 2) F, α = slConjugation F G ∧
      (∃ c : F, (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = c • 1) ∧
      (∀ c : F, (G : Matrix (Fin 2) (Fin 2) F) ≠ c • 1) := by
  have hσ : (gammaOf hodd h3 α).right = 1 := by
    by_contra hσ
    exact not_fixedCond_of_comm α (fun a ha b hb => hfix a b ha hb)
      (fixedCond_of_field_part hodd h3 α hα hσ)
  obtain ⟨G, hG⟩ := eq_slConjugation_of_right_eq_one hodd h3 α hσ
  refine ⟨G, hG, ?_, ?_⟩
  · have h1 : slConjugation F (G * G) = 1 := by rw [map_mul, ← hG, hα]
    obtain ⟨c, hc⟩ := exists_scalar_of_slConjugation_eq_one (G * G) h1
    exact ⟨c, by simpa using hc⟩
  · intro c hc
    exact hne (hG ▸ slConjugation_eq_one_of_scalar G c hc)

end Aut

end CFSG.GH74.GLS.LU.Local
