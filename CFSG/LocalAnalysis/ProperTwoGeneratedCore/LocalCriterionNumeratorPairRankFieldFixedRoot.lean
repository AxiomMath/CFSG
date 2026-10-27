module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

variable {F : Type u} [Field F]

@[expose] def scalarRootFixedSet (sigma : RingAut F) (c : F) : Set F :=
  {y : F | c * sigma y = y}

theorem scalar_norm_one_has_nonzero_fixed [CharP F 2]
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (c : F) (hnorm : c * sigma c = 1) :
    ∃ b : F, b ≠ 0 ∧ c * sigma b = b := by
  by_cases hc : 1 + c = 0
  · have hc1 : c = 1 := (CharTwo.add_eq_zero.mp hc).symm
    subst c
    obtain ⟨d, hd⟩ : ∃ d : F, sigma d ≠ d := by
      by_contra h
      apply hne
      ext d
      exact not_not.mp (not_exists.mp h d)
    refine ⟨d + sigma d, ?_, ?_⟩
    · intro hzero
      exact hd (CharTwo.add_eq_zero.mp hzero).symm
    · rw [one_mul, map_add, field_involution_apply sigma hsigma, add_comm]
  · refine ⟨1 + c, hc, ?_⟩
    rw [map_add, map_one, mul_add, mul_one, hnorm, add_comm]

theorem scalar_fixed_ratio_in_fixed_field
    (sigma : RingAut F) (c b y : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) (hyfixed : c * sigma y = y) :
    y / b ∈ fixedField sigma := by
  apply (mem_fixedField_iff sigma _).mpr
  rw [map_div₀]
  have hsb : sigma b ≠ 0 := by
    intro hzero
    exact hb (sigma.injective (hzero.trans (map_zero sigma).symm))
  apply (div_eq_div_iff hsb hb).mpr
  calc
    sigma y * b = sigma y * (c * sigma b) := by rw [hbfixed]
    _ = (c * sigma y) * sigma b := by ring
    _ = y * sigma b := by rw [hyfixed]

theorem fixed_field_multiple_scalar_fixed
    (sigma : RingAut F) (c b : F) (hbfixed : c * sigma b = b)
    (k : fixedField sigma) : c * sigma ((k : F) * b) = (k : F) * b := by
  rw [map_mul, (mem_fixedField_iff sigma _).mp k.property]
  calc
    c * ((k : F) * sigma b) = (k : F) * (c * sigma b) := by ring
    _ = (k : F) * b := by rw [hbfixed]

@[expose] def scalarRootFixedEquiv
    (sigma : RingAut F) (c b : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) :
    fixedField sigma ≃ scalarRootFixedSet sigma c where
  toFun k := ⟨(k : F) * b, fixed_field_multiple_scalar_fixed sigma c b hbfixed k⟩
  invFun y := ⟨y.val / b,
    scalar_fixed_ratio_in_fixed_field sigma c b y.val hb hbfixed y.property⟩
  left_inv k := by
    apply Subtype.ext
    exact mul_div_cancel_right₀ (k : F) hb
  right_inv y := by
    apply Subtype.ext
    exact div_mul_cancel₀ y.val hb

theorem scalarRootFixedEquiv_apply
    (sigma : RingAut F) (c b : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) (k : fixedField sigma) :
    (scalarRootFixedEquiv sigma c b hb hbfixed k : F) = (k : F) * b := rfl

@[expose] def scalarRootNonzeroFixedEquiv
    (sigma : RingAut F) (c b : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) :
    {k : fixedField sigma // k ≠ 0} ≃ {y : F // c * sigma y = y ∧ y ≠ 0} where
  toFun k := ⟨(k.val : F) * b,
    fixed_field_multiple_scalar_fixed sigma c b hbfixed k.val,
    mul_ne_zero (fun hzero => k.property (Subtype.ext hzero)) hb⟩
  invFun y := ⟨⟨y.val / b,
    scalar_fixed_ratio_in_fixed_field sigma c b y.val hb hbfixed y.property.1⟩,
    fun hzero => y.property.2 (by
      have hval : y.val / b = 0 := congrArg Subtype.val hzero
      exact (div_eq_zero_iff).mp hval |>.resolve_right hb)⟩
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    exact mul_div_cancel_right₀ (k.val : F) hb
  right_inv y := by
    apply Subtype.ext
    exact div_mul_cancel₀ y.val hb

theorem scalar_root_fixed_card [Finite F]
    (sigma : RingAut F) (c b : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) :
    Nat.card (scalarRootFixedSet sigma c) = Nat.card (fixedField sigma) :=
  (Nat.card_congr (scalarRootFixedEquiv sigma c b hb hbfixed)).symm

theorem scalar_root_nonzero_fixed_card [Finite F]
    (sigma : RingAut F) (c b : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) :
    Nat.card {y : F // c * sigma y = y ∧ y ≠ 0} =
      Nat.card (fixedField sigma) - 1 := by
  classical
  have := Fintype.ofFinite (fixedField sigma)
  rw [← Nat.card_congr (scalarRootNonzeroFixedEquiv sigma c b hb hbfixed)]
  simp only [ne_eq]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

theorem scalar_root_fixed_iff_multiple
    (sigma : RingAut F) (c b : F) (hb : b ≠ 0)
    (hbfixed : c * sigma b = b) (y : F) :
    c * sigma y = y ↔ ∃ k : fixedField sigma, y = (k : F) * b := by
  constructor
  · intro hy
    refine ⟨⟨y / b, scalar_fixed_ratio_in_fixed_field sigma c b y hb hbfixed hy⟩, ?_⟩
    exact (div_mul_cancel₀ y hb).symm
  · rintro ⟨k, rfl⟩
    exact fixed_field_multiple_scalar_fixed sigma c b hbfixed k

theorem original_scalar_involution_full_fixed_root_card [Finite F] {n : ℕ}
    (hn : 1 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (sigma : RingAut F) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (c : F) (hnorm : c * sigma c = 1) :
    ∃ s : ℕ, ∃ b : F, 1 ≤ s ∧ n = 2 * s ∧
      (∀ y : F, sigma y = y ^ (2 ^ s)) ∧
      Nat.card (fixedField sigma) = 2 ^ s ∧ b ≠ 0 ∧ c * sigma b = b ∧
      c = b / sigma b ∧
      (∀ y : F, c * sigma y = y ↔ ∃ k : fixedField sigma, y = (k : F) * b) ∧
      Nat.card (scalarRootFixedSet sigma c) = 2 ^ s ∧
      Nat.card {y : F // c * sigma y = y ∧ y ≠ 0} = 2 ^ s - 1 := by
  let : CharP F 2 := char_two_of_card hcard
  obtain ⟨s, hs, hns, hfrob, hfixed⟩ := finite_field_involution_exact hn hcard
    sigma hsigma hne
  obtain ⟨b, hb, hbfixed⟩ := scalar_norm_one_has_nonzero_fixed sigma hsigma hne c hnorm
  have hsb : sigma b ≠ 0 := by
    intro hzero
    exact hb (sigma.injective (hzero.trans (map_zero sigma).symm))
  refine ⟨s, b, hs, hns, hfrob, hfixed, hb, hbfixed,
    (eq_div_iff hsb).mpr hbfixed,
    scalar_root_fixed_iff_multiple sigma c b hb hbfixed, ?_, ?_⟩
  · rw [scalar_root_fixed_card sigma c b hb hbfixed, hfixed]
  · rw [scalar_root_nonzero_fixed_card sigma c b hb hbfixed, hfixed]

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
