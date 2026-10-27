module

public import CFSG.CharacterTheory.PSL2Table.Basic

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem conj_apply_SL (M A : SL(2, F)) (i j : Fin 2) :
    ((M * A * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j =
      ((M : Matrix (Fin 2) (Fin 2) F) i 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 0 +
          (M : Matrix (Fin 2) (Fin 2) F) i 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 0) *
        ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 j +
      ((M : Matrix (Fin 2) (Fin 2) F) i 0 * (A : Matrix (Fin 2) (Fin 2) F) 0 1 +
          (M : Matrix (Fin 2) (Fin 2) F) i 1 * (A : Matrix (Fin 2) (Fin 2) F) 1 1) *
        ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 j := by
  rw [mul_apply_SL, mul_apply_SL, mul_apply_SL]

theorem inv_apply_00 (M : SL(2, F)) :
    ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = (M : Matrix (Fin 2) (Fin 2) F) 1 1 := by
  simp [Matrix.adjugate_fin_two]

theorem inv_apply_01 (M : SL(2, F)) :
    ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = -(M : Matrix (Fin 2) (Fin 2) F) 0 1 := by
  simp [Matrix.adjugate_fin_two]

theorem inv_apply_10 (M : SL(2, F)) :
    ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = -(M : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  simp [Matrix.adjugate_fin_two]

theorem inv_apply_11 (M : SL(2, F)) :
    ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = (M : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  simp [Matrix.adjugate_fin_two]

theorem sq_ne_one_of_ne {a : Fˣ} (h1 : a ≠ 1) (hm1 : a ≠ -1) : (a : F) ^ 2 ≠ 1 := by
  intro h
  rw [sq] at h
  rcases mul_self_eq_one_iff.mp h with h | h
  · exact h1 (Units.ext h)
  · exact hm1 (Units.ext (by rw [h, Units.val_neg, Units.val_one]))

theorem inv_ne_self_of_sq_ne_one {a : Fˣ} (ha : (a : F) ^ 2 ≠ 1) : (a : F)⁻¹ - a ≠ 0 := by
  intro h
  apply ha
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  field_simp at h
  linear_combination -h

theorem conj_diag_mem_splitSL_iff {a : Fˣ} (ha : (a : F) ^ 2 ≠ 1) (M : SL(2, F)) :
    M * diag a * M⁻¹ ∈ splitSL F ↔
      M ∈ splitSL F ∨
        ((M : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) := by
  have hd := inv_ne_self_of_sq_ne_one ha
  have h01 : ((M * diag a * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 0 1 *
        ((a : F)⁻¹ - a) := by
    rw [conj_apply_SL, inv_apply_01, inv_apply_11]
    simp
    ring
  have h10 : ((M * diag a * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -((M : Matrix (Fin 2) (Fin 2) F) 1 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 *
        ((a : F)⁻¹ - a)) := by
    rw [conj_apply_SL, inv_apply_00, inv_apply_10]
    simp
    ring
  have hdet := det_entries M
  rw [mem_splitSL_iff, mem_splitSL_iff, h01, h10, neg_eq_zero, mul_eq_zero, mul_eq_zero,
    mul_eq_zero, mul_eq_zero]
  simp only [hd, or_false]
  constructor
  · rintro ⟨h1 | h1, h2 | h2⟩
    · rw [h1, h2, zero_mul, mul_zero, sub_zero] at hdet
      exact (zero_ne_one hdet).elim
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · rw [h1, h2, zero_mul, mul_zero, sub_zero] at hdet
      exact (zero_ne_one hdet).elim
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Or.inr h1, Or.inl h2⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩

theorem weyl_inv_mul_mem_splitSL {M : SL(2, F)} (h0 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 0)
    (h1 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) : weyl⁻¹ * M ∈ splitSL F := by
  rw [mem_splitSL_iff, mul_apply_SL, mul_apply_SL]
  simp [Matrix.adjugate_fin_two, h0, h1]

theorem mem_splitSL_of_weyl_inv_mul {M : SL(2, F)} (h : weyl⁻¹ * M ∈ splitSL F) :
    (M : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  rw [mem_splitSL_iff, mul_apply_SL, mul_apply_SL] at h
  simp [Matrix.adjugate_fin_two] at h
  exact ⟨h.2, h.1⟩

theorem weyl_not_mem_splitSL : (weyl : SL(2, F)) ∉ splitSL F := by
  rw [mem_splitSL_iff]
  simp

theorem exists_diag_of_mem_splitSL {A : SL(2, F)} (hA : A ∈ splitSL F) :
    ∃ a : Fˣ, A = diag a := by
  obtain ⟨h01, h10⟩ := hA
  have hdet := det_entries A
  rw [h01, zero_mul, sub_zero] at hdet
  have h0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨Units.mk0 _ h0, ?_⟩
  apply SL_ext
  · simp
  · simp [h01]
  · simp [h10]
  · simp only [coe_diag, Units.val_mk0]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact eq_inv_of_mul_eq_one_right hdet

theorem diag_eq_one_or_neg_one_iff (a : Fˣ) : (diag a = 1 ∨ diag a = -1) ↔ (a : F) ^ 2 = 1 := by
  constructor
  · rintro (h | h)
    · have h0 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp at h0
      simp [h0]
    · have h0 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp [neg_apply_SL] at h0
      simp [h0]
  · intro h
    rw [sq] at h
    rcases mul_self_eq_one_iff.mp h with h | h
    · left
      apply SL_ext <;> simp [h]
    · right
      apply SL_ext <;> simp [neg_apply_SL, h]

@[expose] def IsAntiNS (ν : F) (M : SL(2, F)) : Prop :=
  (M : Matrix (Fin 2) (Fin 2) F) 1 1 = -(M : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
    (M : Matrix (Fin 2) (Fin 2) F) 0 1 = -(ν * (M : Matrix (Fin 2) (Fin 2) F) 1 0)

theorem conj_mem_nonsplitSL_iff (h2 : (2 : F) ≠ 0) {ν : F} (hν : ¬ IsSquare ν)
    {C : SL(2, F)} (hC : C ∈ nonsplitSL ν) (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (M : SL(2, F)) :
    M * C * M⁻¹ ∈ nonsplitSL ν ↔ M ∈ nonsplitSL ν ∨ IsAntiNS ν M := by
  obtain ⟨hC1, hC2⟩ := hC
  have hdet := det_entries M
  set α := (M : Matrix (Fin 2) (Fin 2) F) 0 0
  set β := (M : Matrix (Fin 2) (Fin 2) F) 0 1
  set γ := (M : Matrix (Fin 2) (Fin 2) F) 1 0
  set δ := (M : Matrix (Fin 2) (Fin 2) F) 1 1
  set x := (C : Matrix (Fin 2) (Fin 2) F) 0 0
  set y := (C : Matrix (Fin 2) (Fin 2) F) 1 0
  have e00 : ((M * C * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      x + y * (β * δ - ν * α * γ) := by
    rw [conj_apply_SL, inv_apply_00, inv_apply_10, hC1, hC2]
    linear_combination x * hdet
  have e11 : ((M * C * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      x + y * (ν * α * γ - β * δ) := by
    rw [conj_apply_SL, inv_apply_01, inv_apply_11, hC1, hC2]
    linear_combination x * hdet
  have e01 : ((M * C * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      y * (ν * α ^ 2 - β ^ 2) := by
    rw [conj_apply_SL, inv_apply_01, inv_apply_11, hC1, hC2]
    ring
  have e10 : ((M * C * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      y * (δ ^ 2 - ν * γ ^ 2) := by
    rw [conj_apply_SL, inv_apply_00, inv_apply_10, hC1, hC2]
    ring
  rw [mem_nonsplitSL_iff, mem_nonsplitSL_iff, IsAntiNS, e00, e11, e01, e10]
  constructor
  · rintro ⟨h11, h01⟩
    have hI : ν * α * γ = β * δ := by
      have : y * (2 * (ν * α * γ - β * δ)) = 0 := by linear_combination h11
      rcases mul_eq_zero.mp this with h | h
      · exact (hy h).elim
      · rcases mul_eq_zero.mp h with h | h
        · exact (h2 h).elim
        · exact sub_eq_zero.mp h
    have hII : ν * α ^ 2 - β ^ 2 = ν * (δ ^ 2 - ν * γ ^ 2) := by
      have : y * ((ν * α ^ 2 - β ^ 2) - ν * (δ ^ 2 - ν * γ ^ 2)) = 0 := by
        linear_combination h01
      rcases mul_eq_zero.mp this with h | h
      · exact (hy h).elim
      · exact sub_eq_zero.mp h
    have hIII : (α - δ) * (β + ν * γ) = (α + δ) * (β - ν * γ) := by
      linear_combination 2 * hI
    have hIV : ν * ((α - δ) * (α + δ)) = (β - ν * γ) * (β + ν * γ) := by
      linear_combination hII
    by_cases hu : α - δ = 0
    · by_cases hv : β - ν * γ = 0
      · left
        exact ⟨by linear_combination -hu, by linear_combination hv⟩
      · rw [hu, zero_mul] at hIII
        rw [hu, zero_mul, mul_zero] at hIV
        have hu' : α + δ = 0 := by
          rcases mul_eq_zero.mp hIII.symm with h | h
          · exact h
          · exact (hv h).elim
        have hv' : β + ν * γ = 0 := by
          rcases mul_eq_zero.mp hIV.symm with h | h
          · exact (hv h).elim
          · exact h
        right
        exact ⟨by linear_combination hu', by linear_combination hv'⟩
    · by_cases hu' : α + δ = 0
      · rw [hu', zero_mul] at hIII
        have hv' : β + ν * γ = 0 := by
          rcases mul_eq_zero.mp hIII with h | h
          · exact (hu h).elim
          · exact h
        right
        exact ⟨by linear_combination hu', by linear_combination hv'⟩
      · exfalso
        apply hν
        refine ⟨(β - ν * γ) / (α - δ), ?_⟩
        have key : (α + δ) * (ν * (α - δ) ^ 2 - (β - ν * γ) ^ 2) = 0 := by
          linear_combination (α - δ) * hIV + (β - ν * γ) * hIII
        rcases mul_eq_zero.mp key with h | h
        · exact (hu' h).elim
        · field_simp
          linear_combination h
  · rintro (⟨h1, h2'⟩ | ⟨h1, h2'⟩)
    · have h1' : δ = α := h1
      have h2'' : β = ν * γ := h2'
      constructor
      · rw [h1', h2'']
        ring
      · rw [h1', h2'']
        ring
    · have h1' : δ = -α := h1
      have h2'' : β = -(ν * γ) := h2'
      constructor
      · rw [h1', h2'']
        ring
      · rw [h1', h2'']
        ring

theorem antiNS_mul_mem {ν : F} {W M : SL(2, F)} (hW : IsAntiNS ν W) (hM : M ∈ nonsplitSL ν) :
    IsAntiNS ν (W * M) := by
  obtain ⟨hW1, hW2⟩ := hW
  obtain ⟨hM1, hM2⟩ := hM
  constructor
  · rw [mul_apply_SL, mul_apply_SL, hW1, hW2, hM1, hM2]
    ring
  · rw [mul_apply_SL, mul_apply_SL, hW1, hW2, hM1, hM2]
    ring

theorem inv_mul_mem_of_antiNS {ν : F} {W W' : SL(2, F)} (hW : IsAntiNS ν W)
    (hW' : IsAntiNS ν W') : W⁻¹ * W' ∈ nonsplitSL ν := by
  obtain ⟨hW1, hW2⟩ := hW
  obtain ⟨hW1', hW2'⟩ := hW'
  constructor
  · rw [mul_apply_SL, mul_apply_SL, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11,
      hW1, hW2, hW1', hW2']
    ring
  · rw [mul_apply_SL, mul_apply_SL, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11,
      hW1, hW2, hW1', hW2']
    ring

theorem antiNS_conj {ν : F} {W C : SL(2, F)} (hW : IsAntiNS ν W) (hC : C ∈ nonsplitSL ν) :
    W * C * W⁻¹ = C⁻¹ := by
  obtain ⟨hW1, hW2⟩ := hW
  obtain ⟨hC1, hC2⟩ := hC
  have hdet := det_entries W
  rw [hW1, hW2] at hdet
  apply SL_ext <;>
    simp only [conj_apply_SL, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11, hW1, hW2,
      hC1, hC2]
  · linear_combination ((C : Matrix (Fin 2) (Fin 2) F) 0 0) * hdet
  · linear_combination (-(ν * (C : Matrix (Fin 2) (Fin 2) F) 1 0)) * hdet
  · linear_combination (-(C : Matrix (Fin 2) (Fin 2) F) 1 0) * hdet
  · linear_combination ((C : Matrix (Fin 2) (Fin 2) F) 0 0) * hdet

theorem antiNS_not_mem (h2 : (2 : F) ≠ 0) {ν : F} {W : SL(2, F)} (hW : IsAntiNS ν W)
    (hν0 : ν ≠ 0) : W ∉ nonsplitSL ν := by
  rintro ⟨h1, h2'⟩
  obtain ⟨hW1, hW2⟩ := hW
  have hdet := det_entries W
  have ha : (W : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
    have : 2 * (W : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by linear_combination hW1 - h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hc : (W : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : (2 * ν) * (W : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination hW2 - h2'
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hν0)
  rw [ha, hc, zero_mul, mul_zero, sub_zero] at hdet
  exact zero_ne_one hdet

theorem exists_antiNS [Fintype F] (hF : ringChar F ≠ 2) {ν : F} (hν0 : ν ≠ 0) :
    ∃ W : SL(2, F), IsAntiNS ν W := by
  obtain ⟨e, f, h⟩ := exists_normForm_eq hF hν0 (-1)
  refine ⟨⟨!![e, -(ν * f); f, -e], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination -h
  · simp
  · simp

theorem eq_one_or_neg_one_of_mem_nonsplitSL {ν : F} {C : SL(2, F)} (hC : C ∈ nonsplitSL ν)
    (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : C = 1 ∨ C = -1 := by
  obtain ⟨h1, h2⟩ := hC
  have hdet := det_entries C
  simp only [h1, h2, hy, mul_zero, sub_zero] at hdet
  rcases mul_self_eq_one_iff.mp hdet with h | h
  · left
    apply SL_ext <;> simp [h, h1, h2, hy]
  · right
    apply SL_ext <;> simp [neg_apply_SL, h, h1, h2, hy]

theorem conj_unip_apply_00 (M : SL(2, F)) (t : F) :
    ((M * unip t * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      1 - (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 0 * t := by
  have hdet := det_entries M
  rw [conj_apply_SL, inv_apply_00, inv_apply_10]
  simp
  linear_combination hdet

theorem conj_unip_apply_01 (M : SL(2, F)) (t : F) :
    ((M * unip t * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t := by
  rw [conj_apply_SL, inv_apply_01, inv_apply_11]
  simp
  ring

theorem conj_unip_apply_10 (M : SL(2, F)) (t : F) :
    ((M * unip t * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -((M : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 * t) := by
  rw [conj_apply_SL, inv_apply_00, inv_apply_10]
  simp
  ring

theorem conj_unip_apply_11 (M : SL(2, F)) (t : F) :
    ((M * unip t * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 =
      1 + (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 0 * t := by
  have hdet := det_entries M
  rw [conj_apply_SL, inv_apply_01, inv_apply_11]
  simp
  linear_combination hdet

theorem conj_unip_of_borel {M : SL(2, F)} (hM : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (t : F) : M * unip t * M⁻¹ = unip ((M : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
  apply SL_ext
  · rw [conj_unip_apply_00, hM]; simp
  · rw [conj_unip_apply_01]; simp
  · rw [conj_unip_apply_10, hM]; simp
  · rw [conj_unip_apply_11, hM]; simp

end CFSG.PSL2Table
