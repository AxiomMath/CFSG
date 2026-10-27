module

public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectiveLineFixedPoints

public section

namespace CFSG.Semidihedral.UnitaryBranch

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.Principal

variable (F : Type) [Field F]

@[expose] noncomputable def translationHom : Multiplicative F →* Equiv.Perm (Omega F) where
  toFun b := translation F (Multiplicative.toAdd b)
  map_one' := translation_zero
  map_mul' _ _ := translation_add _ _

@[expose] noncomputable def multiplierHom : Fˣ →* Equiv.Perm (Omega F) where
  toFun c := multiplier F c
  map_one' := by
    refine Equiv.ext fun x => ?_
    cases x <;> simp
  map_mul' a b := by
    refine Equiv.ext fun x => ?_
    cases x with
    | none => rfl
    | some x => simp [mul_assoc]

theorem translationHom_apply (b : Multiplicative F) :
    translationHom F b = translation F (Multiplicative.toAdd b) := rfl

theorem multiplierHom_apply (c : Fˣ) : multiplierHom F c = multiplier F c := rfl

theorem translationHom_injective : Function.Injective (translationHom F) := by
  intro a b h
  have h1 := congrArg (fun d : Equiv.Perm (Omega F) => d (some 0)) h
  simp only [translationHom_apply, translation_some, zero_add, Option.some.injEq] at h1
  exact h1

theorem multiplierHom_injective : Function.Injective (multiplierHom F) := by
  intro a b h
  have h1 := congrArg (fun d : Equiv.Perm (Omega F) => d (some 1)) h
  simp only [multiplierHom_apply, multiplier_some, mul_one, Option.some.injEq] at h1
  exact Units.ext h1

theorem translation_mem_coordinateD (b : F) : translation F b ∈ coordinateD F :=
  Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)))

theorem inversion_mem_coordinateD : inversion F ∈ coordinateD F :=
  Subgroup.subset_closure (Or.inl (Subgroup.subset_closure (Or.inr rfl)))

theorem multiplier_mem_coordinateD (c : Fˣ) : multiplier F c ∈ coordinateD F :=
  Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem translationHom_range_le : (translationHom F).range ≤ coordinateD F := by
  rintro _ ⟨b, rfl⟩
  exact translation_mem_coordinateD F _

theorem multiplierHom_range_le : (multiplierHom F).range ≤ coordinateD F := by
  rintro _ ⟨c, rfl⟩
  exact multiplier_mem_coordinateD F _

theorem multiplier_conj_translation (c : Fˣ) (b : F) :
    multiplier F c * translation F b * (multiplier F c)⁻¹ = translation F (c * b) := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rfl
  | some x =>
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have hinv : (multiplier F c)⁻¹ (some x) = some ((c⁻¹ : Fˣ) * x) := by
      rw [Equiv.Perm.inv_eq_iff_eq, multiplier_some, ← mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, one_mul]
    rw [hinv, translation_some, multiplier_some, translation_some, mul_add, ← mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem inversion_mul_self : inversion F * inversion F = 1 := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => simp
  | some x =>
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [Equiv.Perm.mul_apply, inversion_nonzero F x hx,
        inversion_nonzero F _ (neg_ne_zero.mpr (inv_ne_zero hx))]
      simp

theorem inversion_inv : (inversion F)⁻¹ = inversion F :=
  inv_eq_of_mul_eq_one_right (inversion_mul_self F)

theorem inversion_conj_multiplier (c : Fˣ) :
    inversion F * multiplier F c * (inversion F)⁻¹ = multiplier F c⁻¹ := by
  rw [inversion_inv]
  refine Equiv.ext fun x => ?_
  cases x with
  | none =>
    simp [Equiv.Perm.mul_apply]
  | some x =>
    by_cases hx : x = 0
    · subst hx
      simp [Equiv.Perm.mul_apply]
    · have hcx : -((c : F) * -x⁻¹) ≠ 0 := by
        simp [hx]
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inversion_nonzero F x hx, multiplier_some,
        inversion_nonzero F _ (by simpa using hcx), multiplier_some]
      congr 1
      field_simp
      simp

theorem multiplier_apply_eq_self_iff {c : Fˣ} (hc : c ≠ 1) (x : Omega F) :
    multiplier F c x = x ↔ x = none ∨ x = some 0 := by
  cases x with
  | none => simp
  | some x =>
    simp only [multiplier_some, Option.some.injEq, reduceCtorEq, false_or]
    constructor
    · intro h
      by_contra hx
      apply hc
      apply Units.ext
      have := mul_right_cancel₀ hx (h.trans (one_mul x).symm)
      simpa using this
    · rintro rfl
      simp

theorem eq_translation_of_commute {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F) {b : F}
    (hb : b ≠ 0) (hcomm : d * translation F b = translation F b * d) :
    ∃ c : F, d = translation F c := by
  obtain ⟨A, rfl⟩ := exists_coordinateGLAction_eq hd
  have hinf : coordinateGLAction F A none = none := by
    have h1 := congrArg (fun e : Equiv.Perm (Omega F) => e none) hcomm
    simp only [Equiv.Perm.mul_apply, translation_none] at h1
    cases h2 : coordinateGLAction F A none with
    | none => rfl
    | some y =>
      rw [h2, translation_some, Option.some.injEq] at h1
      exact absurd (by simpa using h1.symm) hb
  have hc : A.val 1 0 = 0 := by
    by_contra hc
    rw [coordinateGLAction_infinity F A hc] at hinf
    exact Option.some_ne_none _ hinf
  have hdet : A.val 0 0 * A.val 1 1 ≠ 0 := by
    have h := A.det_ne_zero
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at h
    exact h
  have hd1 : A.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  have hfin : ∀ x : F, coordinateGLAction F A (some x) =
      some ((A.val 0 0 * x + A.val 0 1) / A.val 1 1) := by
    intro x
    rw [coordinateGLAction_finite F A x (by rw [hc, zero_mul, zero_add]; exact hd1), hc,
      zero_mul, zero_add]
  have h00 : A.val 0 0 = A.val 1 1 := by
    have h1 := congrArg (fun e : Equiv.Perm (Omega F) => e (some 0)) hcomm
    simp only [Equiv.Perm.mul_apply, translation_some, zero_add, hfin, mul_zero,
      Option.some.injEq] at h1
    field_simp at h1
    have h2 : A.val 0 0 * b = A.val 1 1 * b := by linear_combination h1
    exact mul_right_cancel₀ hb h2
  refine ⟨A.val 0 1 / A.val 1 1, ?_⟩
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rw [hinf, translation_none]
  | some x =>
    rw [hfin, translation_some, h00]
    congr 1
    field_simp

theorem eq_multiplier_or_of_preserves {d : Equiv.Perm (Omega F)} (hd : d ∈ coordinateD F)
    (h : (d none = none ∧ d (some 0) = some 0) ∨ (d none = some 0 ∧ d (some 0) = none)) :
    (∃ μ : Fˣ, d = multiplier F μ) ∨ ∃ μ : Fˣ, d = multiplier F μ * inversion F := by
  obtain ⟨A, rfl⟩ := exists_coordinateGLAction_eq hd
  have hdet := A.det_ne_zero
  rw [Matrix.det_fin_two] at hdet
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hc : A.val 1 0 = 0 := by
      by_contra hc
      rw [coordinateGLAction_infinity F A hc] at h1
      exact Option.some_ne_none _ h1
    rw [hc, mul_zero, sub_zero] at hdet
    have ha : A.val 0 0 ≠ 0 := left_ne_zero_of_mul hdet
    have hd' : A.val 1 1 ≠ 0 := right_ne_zero_of_mul hdet
    have hfin : ∀ x : F, coordinateGLAction F A (some x) =
        some ((A.val 0 0 * x + A.val 0 1) / A.val 1 1) := by
      intro x
      rw [coordinateGLAction_finite F A x (by rw [hc, zero_mul, zero_add]; exact hd'), hc,
        zero_mul, zero_add]
    have hb : A.val 0 1 = 0 := by
      rw [hfin, mul_zero, zero_add, Option.some.injEq, div_eq_zero_iff] at h2
      exact h2.resolve_right hd'
    refine Or.inl ⟨Units.mk0 (A.val 0 0 / A.val 1 1) (div_ne_zero ha hd'), ?_⟩
    refine Equiv.ext fun x => ?_
    cases x with
    | none => rw [h1, multiplier_none]
    | some x =>
      rw [hfin, multiplier_some, hb, add_zero, Units.val_mk0]
      congr 1
      ring
  ·
    have hc : A.val 1 0 ≠ 0 := by
      intro hc
      rw [coordinateGLAction_infinity_lower_left_zero F A hc] at h1
      exact Option.some_ne_none _ h1.symm
    have ha : A.val 0 0 = 0 := by
      rw [coordinateGLAction_infinity F A hc, Option.some.injEq, div_eq_zero_iff] at h1
      exact h1.resolve_right hc
    have hd' : A.val 1 1 = 0 := by
      by_contra hd'
      rw [coordinateGLAction_finite F A 0 (by rw [mul_zero, zero_add]; exact hd')] at h2
      exact Option.some_ne_none _ h2
    rw [ha, hd', zero_mul, zero_sub, neg_ne_zero] at hdet
    have hb : A.val 0 1 ≠ 0 := left_ne_zero_of_mul hdet
    refine Or.inr ⟨Units.mk0 (-(A.val 0 1 / A.val 1 0)) (neg_ne_zero.mpr (div_ne_zero hb hc)),
      ?_⟩
    refine Equiv.ext fun x => ?_
    cases x with
    | none =>
      rw [Equiv.Perm.mul_apply, inversion_none, multiplier_some, mul_zero,
        coordinateGLAction_infinity F A hc, ha, zero_div]
    | some x =>
      by_cases hx : x = 0
      · subst hx
        rw [h2, Equiv.Perm.mul_apply, inversion_zero, multiplier_none]
      · rw [Equiv.Perm.mul_apply, inversion_nonzero F x hx, multiplier_some, Units.val_mk0,
          coordinateGLAction_finite F A x (by rw [hd', add_zero]; exact mul_ne_zero hc hx), ha,
          hd', zero_mul, zero_add, add_zero]
        congr 1
        field_simp

theorem preserves_of_conj_multiplier {d : Equiv.Perm (Omega F)} {c c' : Fˣ} (hc : c ≠ 1)
    (hc' : c' ≠ 1) (hconj : d * multiplier F c * d⁻¹ = multiplier F c') :
    (d none = none ∧ d (some 0) = some 0) ∨ (d none = some 0 ∧ d (some 0) = none) := by
  have hfix : ∀ x, multiplier F c x = x → multiplier F c' (d x) = d x := by
    intro x hx
    rw [← hconj]
    simp [Equiv.Perm.mul_apply, hx]
  have h1 := (multiplier_apply_eq_self_iff F hc' (d none)).mp
    (hfix none ((multiplier_apply_eq_self_iff F hc none).mpr (Or.inl rfl)))
  have h2 := (multiplier_apply_eq_self_iff F hc' (d (some 0))).mp
    (hfix (some 0) ((multiplier_apply_eq_self_iff F hc (some 0)).mpr (Or.inr rfl)))
  have hne : d none ≠ d (some 0) := fun h => Option.some_ne_none 0 (d.injective h).symm
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem card_coordinateD [Finite F] :
    Nat.card (coordinateD F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← Nat.card_congr (pglEquivCoordinateD F).toEquiv]
  exact CFSG.GorensteinWalter.pgl2_card_formula F

end CFSG.Semidihedral.UnitaryBranch
