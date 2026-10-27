module

public import CFSG.CGT.Timmesfeld75.L2Aut

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Involution

variable {F : Type} [Field F]

theorem aiv_of_involution [CharP F 2] {g : SL(2, F)} {σ : F ≃+* F}
    (hφ : ∀ x : SL(2, F), g * sl2FieldAut σ (g * sl2FieldAut σ x * g⁻¹) * g⁻¹ = x) :
    g * sl2FieldAut σ g = 1 ∧ ∀ s, σ (σ s) = s := by
  have key : ∀ x : SL(2, F), (g * sl2FieldAut σ g) * sl2FieldAut σ (sl2FieldAut σ x) *
      (g * sl2FieldAut σ g)⁻¹ = x := fun x => by
    refine Eq.trans ?_ (hφ x)
    simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
  set h : SL(2, F) := g * sl2FieldAut σ g
  have hu : ∀ s : F, h * utriElt (σ (σ s)) * h⁻¹ = utriElt s := fun s => by
    simpa only [sl2FieldAut_utriElt] using key (utriElt s)
  have hl : ∀ t : F, h * ltriElt (σ (σ t)) * h⁻¹ = ltriElt t := fun t => by
    simpa only [sl2FieldAut_ltriElt] using key (ltriElt t)
  have h10 : h 1 0 = 0 := by
    have h1 := congrArg (fun x : SL(2, F) => x 1 0) (hu 1)
    simp only [conj_utriElt_apply_10, utriElt_apply_10, map_one, mul_one] at h1
    have h2 : h 1 0 ^ 2 = 0 := by linear_combination (-1 : F) * h1
    exact pow_eq_zero_iff two_ne_zero |>.1 h2
  have h01 : h 0 1 = 0 := by
    have h1 := congrArg (fun x : SL(2, F) => x 0 1) (hl 1)
    simp only [conj_ltriElt_apply_01, ltriElt_apply_01, map_one, mul_one] at h1
    have h2 : h 0 1 ^ 2 = 0 := by linear_combination (-1 : F) * h1
    exact pow_eq_zero_iff two_ne_zero |>.1 h2
  have hsq : ∀ s : F, h 0 0 ^ 2 * σ (σ s) = s := fun s => by
    have h1 := congrArg (fun x : SL(2, F) => x 0 1) (hu s)
    simpa only [conj_utriElt_apply_01, utriElt_apply_01] using h1
  have h00 : h 0 0 = 1 := by
    have h1 := hsq 1
    rw [map_one, map_one, mul_one] at h1
    exact CharTwo.sq_injective (by simpa using h1)
  have h11 : h 1 1 = 1 := by
    have hd := sl2_det h
    rw [h01, h00] at hd
    linear_combination hd
  have hh1 : h = 1 := sl2_ext (by rw [h00, one_apply_00]) (by rw [h01, one_apply_01])
    (by rw [h10, one_apply_10]) (by rw [h11, one_apply_11])
  refine ⟨hh1, fun s => ?_⟩
  have h1 := hsq s
  rwa [h00, one_pow, one_mul] at h1

end Involution

section Hilbert90

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem aiv_exists_entries {σ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F) (hσσ : ∀ s, σ (σ s) = s)
    {a b c d : F} (hd : a * d - b * c = 1) (ha : σ a = d) (hda : σ d = a) (hb : σ b = b)
    (hc : σ c = c) :
    ∃ x y z w : F, x * w - y * z = 1 ∧ σ x = x * a + y * c ∧ σ y = x * b + y * d ∧
      σ z = z * a + w * c ∧ σ w = z * b + w * d := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hfix : ∀ l : F, σ ((l + σ l * d) * (l + σ l * a) - σ l * b * (σ l * c)) =
      (l + σ l * d) * (l + σ l * a) - σ l * b * (σ l * c) := fun l => by
    simp only [map_sub, map_mul, map_add, hσσ, ha, hda, hb, hc]
    linear_combination (l ^ 2 - σ l ^ 2) * hd
  obtain ⟨l, hl⟩ : ∃ l : F, (l + σ l * d) * (l + σ l * a) - σ l * b * (σ l * c) ≠ 0 := by
    by_cases ht : a + d = 0
    · obtain ⟨l, hl⟩ : ∃ l : F, σ l ≠ l := by
        by_contra hall
        exact hσ (RingEquiv.ext fun x => by_contra fun hx => hall ⟨x, hx⟩)
      refine ⟨l, fun h => hl ?_⟩
      have h1 : (l + σ l) ^ 2 = 0 := by
        linear_combination h + (l * σ l) * h2 - (l * σ l) * ht - σ l ^ 2 * hd
      have h3 : l + σ l = 0 := pow_eq_zero_iff two_ne_zero |>.1 h1
      exact (CharTwo.add_eq_zero.1 h3).symm
    · refine ⟨1, fun h => ht ?_⟩
      rw [map_one] at h
      linear_combination h - hd - h2
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2)
    ((l + σ l * d) * (l + σ l * a) - σ l * b * (σ l * c))
  have hμ0 : μ ≠ 0 := fun h => hl (by rw [hμ, h, zero_mul])
  have hσμ : σ μ = μ := by
    apply CharTwo.sq_injective
    simp only [sq]
    rw [← map_mul, ← hμ, hfix l]
  refine ⟨μ⁻¹ * (l + σ l * d), μ⁻¹ * (σ l * b), μ⁻¹ * (σ l * c), μ⁻¹ * (l + σ l * a),
    ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    linear_combination hμ
  · simp only [map_mul, map_inv₀, map_add, hσσ, hσμ, hda]
    linear_combination (-(μ⁻¹ * σ l)) * hd - (μ⁻¹ * σ l * b * c) * h2
  · simp only [map_mul, map_inv₀, hσσ, hσμ, hb]
    linear_combination (-(μ⁻¹ * σ l * b * d)) * h2
  · simp only [map_mul, map_inv₀, hσσ, hσμ, hc]
    linear_combination (-(μ⁻¹ * σ l * a * c)) * h2
  · simp only [map_mul, map_inv₀, map_add, hσσ, hσμ, ha]
    linear_combination (-(μ⁻¹ * σ l)) * hd - (μ⁻¹ * σ l * b * c) * h2

theorem aiv_exists_sl2FieldAut_eq_mul {σ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F)
    (hσσ : ∀ s, σ (σ s) = s) {g : SL(2, F)} (hg : g * sl2FieldAut σ g = 1) :
    ∃ k : SL(2, F), sl2FieldAut σ k = k * g := by
  have hτ : sl2FieldAut σ g = g⁻¹ := eq_inv_of_mul_eq_one_right hg
  have e00 : σ (g 0 0) = g 1 1 := by
    have h1 := congrArg (fun x : SL(2, F) => x 0 0) hτ
    simpa only [sl2FieldAut_apply_00, inv_apply_00] using h1
  have e01 : σ (g 0 1) = g 0 1 := by
    have h1 := congrArg (fun x : SL(2, F) => x 0 1) hτ
    simpa only [sl2FieldAut_apply_01, inv_apply_01, CharTwo.neg_eq] using h1
  have e10 : σ (g 1 0) = g 1 0 := by
    have h1 := congrArg (fun x : SL(2, F) => x 1 0) hτ
    simpa only [sl2FieldAut_apply_10, inv_apply_10, CharTwo.neg_eq] using h1
  have e11 : σ (g 1 1) = g 0 0 := by
    have h1 := congrArg (fun x : SL(2, F) => x 1 1) hτ
    simpa only [sl2FieldAut_apply_11, inv_apply_11] using h1
  obtain ⟨x, y, z, w, hdet, hx, hy, hz, hw⟩ :=
    aiv_exists_entries hσ hσσ (sl2_det g) e00 e11 e01 e10
  obtain ⟨k, k00, k01, k10, k11⟩ : ∃ k : SL(2, F), k 0 0 = x ∧ k 0 1 = y ∧ k 1 0 = z ∧
      k 1 1 = w :=
    ⟨⟨!![x, y; z, w], by rw [Matrix.det_fin_two_of]; exact hdet⟩, rfl, rfl, rfl, rfl⟩
  refine ⟨k, sl2_ext ?_ ?_ ?_ ?_⟩
  · rw [sl2FieldAut_apply_00, mul_apply_00, k00, k01]
    exact hx
  · rw [sl2FieldAut_apply_01, mul_apply_01, k00, k01]
    exact hy
  · rw [sl2FieldAut_apply_10, mul_apply_10, k10, k11]
    exact hz
  · rw [sl2FieldAut_apply_11, mul_apply_11, k10, k11]
    exact hw

end Hilbert90

theorem autInvol_inner_or_field {F : Type} [Field F] [Finite F] [CharP F 2]
    (φ : SL(2, F) ≃* SL(2, F)) (hφ : ∀ x, φ (φ x) = x) :
    (∃ g : SL(2, F), g * g = 1 ∧ ∀ x, φ x = g * x * g⁻¹) ∨
    ∃ (k : SL(2, F)) (σ : F ≃+* F), σ ≠ RingEquiv.refl F ∧
      ∀ x, k * φ x * k⁻¹ = Matrix.SpecialLinearGroup.map (σ : F →+* F) (k * x * k⁻¹) := by
  obtain ⟨g, σ, hg⟩ := exists_eq_conj_sl2FieldAut φ
  have hinv : ∀ x : SL(2, F), g * sl2FieldAut σ (g * sl2FieldAut σ x * g⁻¹) * g⁻¹ = x :=
    fun x => by
      have h1 := hφ x
      rwa [hg x, hg (g * sl2FieldAut σ x * g⁻¹)] at h1
  obtain ⟨hgg, hσσ⟩ := aiv_of_involution hinv
  by_cases hσ : σ = RingEquiv.refl F
  · left
    subst hσ
    refine ⟨g, ?_, fun x => ?_⟩
    · rw [sl2FieldAut_refl] at hgg
      exact hgg
    · rw [hg x, sl2FieldAut_refl]
      rfl
  · right
    obtain ⟨k, hk⟩ := aiv_exists_sl2FieldAut_eq_mul hσ hσσ hgg
    refine ⟨k, σ, hσ, fun x => ?_⟩
    rw [hg x, ← sl2FieldAut_eq_map]
    simp only [map_mul, map_inv, hk]
    group

end CFSG.CGT.Timmesfeld75
