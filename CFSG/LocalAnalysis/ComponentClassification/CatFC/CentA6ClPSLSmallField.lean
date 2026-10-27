module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallBasic

public noncomputable section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.ComponentClassification.CatFC.PSLSmall

section Field2

variable {K : Type} [Field K] [Finite K]

theorem exists_sq_of_fixedField (hodd : ringChar K ≠ 2) {τ : K ≃+* K} (hτ2 : τ ^ 2 = 1)
    (hτ : τ ≠ 1) (u : (fixedField K τ)ˣ) :
    ∃ c : Kˣ, c ^ 2 = Units.map (fixedField K τ).subtype u := by
  letI : Fintype K := Fintype.ofFinite K
  have hcard := fixedField_card_square K τ hτ2 hτ
  set q₀ := Nat.card (fixedField K τ) with hq₀
  have hoddK : ¬ Even (Nat.card K) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd))
  have hq0 : ¬ Even q₀ := fun h => hoddK (by
    rw [hcard]; exact Nat.even_pow.mpr ⟨h, by norm_num⟩)
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hq0
  set a : Kˣ := Units.map (fixedField K τ).subtype u with ha
  have hpow : a ^ (q₀ - 1) = 1 := by
    have h1 : u ^ (q₀ - 1) = 1 := by
      have := pow_card_eq_one' (G := (fixedField K τ)ˣ) (x := u)
      rwa [Nat.card_units] at this
    rw [ha, ← map_pow, h1, map_one]
  have hdiv : Fintype.card K / 2 = (q₀ - 1) * (k + 1) := by
    rw [← Nat.card_eq_fintype_card, hcard, hk]
    have : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
    rw [this]
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]
    omega
  have hsq : IsSquare (a : K) := by
    rw [FiniteField.isSquare_iff hodd a.ne_zero, hdiv, pow_mul]
    have : (a : K) ^ (q₀ - 1) = 1 := by
      have := congrArg Units.val hpow
      simpa using this
    rw [this, one_pow]
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    intro h0
    apply a.ne_zero
    rw [hr, h0, mul_zero]
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply Units.ext
  simp [sq, hr]

@[expose] def detClass (F : Type) [Field F] :
    ProjGenLinGroup (Fin 2) F →* Fˣ ⧸ (powMonoidHom 2 : Fˣ →* Fˣ).range :=
  ProjGenLinGroup.lift ((QuotientGroup.mk' (powMonoidHom 2 : Fˣ →* Fˣ).range).comp
      Matrix.GeneralLinearGroup.det) (by
    apply MonoidHom.ext
    intro c
    simp only [MonoidHom.comp_apply, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      MonoidHom.one_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨c, rfl⟩)

theorem detClass_mk {F : Type} [Field F] (g : GL (Fin 2) F) :
    detClass F (ProjGenLinGroup.mk g) =
      QuotientGroup.mk (Matrix.GeneralLinearGroup.det g) := by
  unfold detClass
  rw [ProjGenLinGroup.lift_mk]
  rfl

theorem exists_outer_involution_pgl_two {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (hneg : IsSquare (-1 : F)) :
    ∃ x : ProjGenLinGroup (Fin 2) F, x ^ 2 = 1 ∧ detClass F x ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := FiniteField.exists_nonsquare hodd
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    exact hζ ⟨0, by simp⟩
  have hdet : (!![0, 1; ζ, 0] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using hζ0
  let g₀ : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet
  have hg₀ : g₀.val = !![0, 1; ζ, 0] := rfl
  refine ⟨ProjGenLinGroup.mk g₀, ?_, ?_⟩
  · rw [← map_pow]
    have : g₀ ^ 2 = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ζ hζ0) := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, sq, hg₀]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [this]
    exact ProjGenLinGroup.mk_scalar _
  · rw [detClass_mk]
    intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 : ((c : F)) ^ 2 = -ζ := by
      have := congrArg Units.val hc
      simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val] at this
      rw [this, Matrix.GeneralLinearGroup.val_det_apply, hg₀, Matrix.det_fin_two_of]
      ring
    have hsq : IsSquare (-ζ) := ⟨(c : F), by rw [← h2]; ring⟩
    apply hζ
    have : ζ = (-1) * (-ζ) := by ring
    rw [this]
    exact hneg.mul hsq

theorem field_two_evidence (hK : Nat.card K = 81) {τ : K ≃+* K} (hτ2 : τ ^ 2 = 1) (hτ : τ ≠ 1) :
    OuterEvidence (pslFieldAut (Fin 2) K τ) := by
  have hoddK : Odd (Nat.card K) := by rw [hK]; decide
  have hodd := CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hoddK
  have hcard := fixedField_card_square K τ hτ2 hτ
  have hq0 : Nat.card (fixedField K τ) = 9 := by
    have h2 : Nat.card (fixedField K τ) ^ 2 = 9 ^ 2 := by
      rw [← hcard, hK]
      norm_num
    exact Nat.pow_left_injective two_ne_zero h2
  have hodd0 : ringChar (fixedField K τ) ≠ 2 :=
    CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card _ (by rw [hq0]; decide)
  have hneg : IsSquare (-1 : fixedField K τ) := by
    letI : Fintype (fixedField K τ) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hq0]
    decide
  obtain ⟨x₀, hx₀2, hx₀⟩ := exists_outer_involution_pgl_two hodd0 hneg
  let e1 := fixedPSLEquivT 2 K τ
  let e2 := subfieldPGLEquivFixed (Fin 2) K τ
  let ι : fixedPSL 2 K τ →* ProjGenLinGroup (Fin 2) (fixedField K τ) :=
    e2.symm.toMonoidHom.comp ((fixedT 2 K τ).subtype.comp e1.toMonoidHom)
  have hι : Function.Injective ι := by
    intro a b hab
    have h1 : ((fixedT 2 K τ).subtype.comp e1.toMonoidHom) a =
        ((fixedT 2 K τ).subtype.comp e1.toMonoidHom) b := e2.symm.injective hab
    exact e1.injective (Subtype.val_injective h1)
  have hmem : e2 x₀ ∈ fixedT 2 K τ := by
    obtain ⟨B, rfl⟩ := ProjGenLinGroup.mk_surjective x₀
    change (e2 (ProjGenLinGroup.mk B)).val ∈ pslRange 2 K
    rw [subfieldPGLEquivFixed_val, subfield_projectivity_mem_pslRange_iff]
    exact exists_sq_of_fixedField hodd hτ2 hτ (Matrix.GeneralLinearGroup.det B)
  let x : fixedPSL 2 K τ := e1.symm ⟨e2 x₀, hmem⟩
  have hιx : ι x = x₀ := by
    change e2.symm ((fixedT 2 K τ).subtype (e1 (e1.symm ⟨e2 x₀, hmem⟩))) = x₀
    rw [MulEquiv.apply_symm_apply]
    exact e2.symm_apply_apply x₀
  have hψ : (detClass (fixedField K τ)).comp ι x ≠ 1 := by
    rw [MonoidHom.comp_apply, hιx]
    exact hx₀
  have hx2 : x ^ 2 = 1 := by
    apply hι
    rw [map_pow, hιx, hx₀2, map_one]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hψ
    rw [h1, map_one]
  exact ⟨x, (fixedField K τ)ˣ ⧸ (powMonoidHom 2 : (fixedField K τ)ˣ →* (fixedField K τ)ˣ).range,
    inferInstance, (detClass (fixedField K τ)).comp ι, orderOf_eq_prime hx2 hx1, hψ⟩

end Field2

end CFSG.ComponentClassification.CatFC.PSLSmall
