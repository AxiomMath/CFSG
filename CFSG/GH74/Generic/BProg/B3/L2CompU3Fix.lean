module

public import CFSG.GH74.Generic.S45.LUniFix
public import CFSG.GH74.Generic.BProg.B3.L2CompU3Conj
public import CFSG.GH74.Generic.BProg.B3.L2CompU3Vec

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompU3Fix

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.GH74.Generic.S45.Uni CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def FixConclD8 (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (ψ : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ c d : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
    (d.map h.bar)ᵀ * d = 1 ∧ d.det = 1 ∧
    (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ d * d = 1 ∧ d * c * d = c * c * c ∧
      A * ψ c = c * A ∧ A * ψ d = d * A

theorem class1b_odd_D8 (hodd : Odd n) (h2 : (2 : K) ≠ 0) :
    ∀ (A : Matrix (Fin n) (Fin n) K) (l : K), (A.map h.bar)ᵀ * A = 1 →
      A * A = (l * l) • 1 → h.bar l * l = -1 → FixConclD8 h n A id := by
  intro A l hAu hAA hNl
  exfalso
  have hd1 := det_unitary_norm h hAu
  have hd2 : A.det * A.det = l ^ n * l ^ n := by
    have := congrArg Matrix.det hAA
    rw [det_mul, det_smul, det_one, Fintype.card_fin] at this
    rw [this]
    ring
  have hN : h.bar (l ^ n) * l ^ n = -1 := by
    rw [map_pow, ← mul_pow, hNl, hodd.neg_one_pow]
  have hd : A.det = l ^ n ∨ A.det = -l ^ n := by
    have : (A.det - l ^ n) * (A.det + l ^ n) = 0 := by linear_combination hd2
    rcases mul_eq_zero.1 this with h3 | h3
    · exact Or.inl (sub_eq_zero.1 h3)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h3)
  rcases hd with hd | hd
  · rw [hd, hN] at hd1
    exact h2 (by linear_combination -hd1)
  · rw [hd, map_neg, neg_mul_neg, hN] at hd1
    exact h2 (by linear_combination -hd1)

theorem class2alt_odd_D8 (hodd : Odd n) (h2 : (2 : K) ≠ 0) :
    ∀ A : Matrix (Fin n) (Fin n) K, (A.map h.bar)ᵀ * A = 1 → A * A.map h.bar = (-1 : K) • 1 →
      FixConclD8 h n A (fun M => M.map h.bar) := by
  intro A hAu hAA
  exfalso
  obtain ⟨-, hAt'⟩ := class2_transpose h hAu hAA
  have hd1 := det_unitary_norm h hAu
  have h3 : A.det = -A.det := by
    have := congrArg Matrix.det hAt'
    rw [det_transpose, det_smul, Fintype.card_fin, hodd.neg_pow, one_pow] at this
    linear_combination this
  have h4 : A.det = 0 := by
    have : (2 : K) * A.det = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [h4, map_zero, zero_mul] at hd1
  exact zero_ne_one hd1

theorem fixed_class1_D8 (hp : p ≠ 2) (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hAu : (A.map h.bar)ᵀ * A = 1) {μ : K} (hμ : A * A = μ • 1) : FixConclD8 h 3 A id := by
  have hA' : A = μ • (A.map h.bar)ᵀ := by
    calc A = ((A.map h.bar)ᵀ * A) * A := by rw [hAu, Matrix.one_mul]
      _ = (A.map h.bar)ᵀ * (A * A) := by rw [Matrix.mul_assoc]
      _ = μ • (A.map h.bar)ᵀ := by rw [hμ, Matrix.mul_smul, Matrix.mul_one]
  have hA0 := ne_zero_of_unitary h (by omega) hAu
  have hA'' : (A.map h.bar)ᵀ = h.bar μ • A := by
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => (M.map h.bar)ᵀ) hA'
    simp only [ustar_smul, ustar_ustar] at this
    exact this
  have hμN : h.bar μ * μ = 1 := by
    have e : μ • (h.bar μ • A) = A := by rw [← hA'', ← hA']
    have h3 : (1 - μ * h.bar μ) • A = 0 := by
      rw [sub_smul, one_smul, ← smul_smul, e, sub_self]
    have := (smul_eq_zero.1 h3).resolve_right hA0
    linear_combination -this
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    simp at hμN
  obtain ⟨l, hl⟩ := isSquare_of_norm_one h hp hμN
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [hl]; ring)
  have hNl : (h.bar l * l) * (h.bar l * l) = 1 := by
    have : h.bar μ * μ = (h.bar l * l) * (h.bar l * l) := by
      rw [hl, map_mul]; ring
    rw [← this, hμN]
  rcases mul_self_eq_one_iff.1 hNl with hN1 | hN1
  · set T : Matrix (Fin 3) (Fin 3) K := l⁻¹ • A with hT
    have hTa : ∀ z w, stdHermForm h 3 (T *ᵥ z) w = stdHermForm h 3 z (T *ᵥ w) := by
      intro z w
      rw [hT, smul_mulVec, smul_mulVec, map_smulₛₗ, LinearMap.smul_apply, map_smul,
        hh_mulVec_left, hA'', smul_mulVec, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have hbl : h.bar l = l⁻¹ := eq_inv_of_mul_eq_one_left hN1
      rw [map_inv₀, hbl, hl, map_mul, hbl, inv_inv]
      field_simp
    have hT2 : T * T = 1 := by
      rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hμ, smul_smul, hl]
      have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
      rw [this, one_smul]
    obtain ⟨x, y, ε, hε, hx, hy, hxx, hyy, hxy⟩ := exists_eigenpair h h2 (le_refl 3) hTa hT2
    obtain ⟨d, hd1, hd2, hd3, hd4, hd5⟩ :=
      L2CompU3Vec.exists_inner_d h hε hTa hxx hyy hxy hx hy
    have hAT : A = l • T := by rw [hT, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    refine ⟨pairRot h x y, d, unitary_of_isometry h (pairRot_isometry h hxx hyy hxy),
      pairRot_det h hxx hyy hxy, hd1, hd2, pairRot_not_scalar h hxx hyy hxy h2 (le_refl 3),
      pairRot_pow_four h hxx hyy hxy, hd3, hd4, ?_, ?_⟩
    · show A * pairRot h x y = pairRot h x y * A
      rw [hAT, Matrix.smul_mul, Matrix.mul_smul, pairRot_comm h hε hTa hx hy]
    · show A * d = d * A
      rw [hAT, Matrix.smul_mul, Matrix.mul_smul, hd5]
  · exact class1b_odd_D8 h (by decide) h2 A l hAu (by rw [hμ, hl]) hN1

theorem fixed_class2_D8 (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hAu : (A.map h.bar)ᵀ * A = 1) {μ : K} (hμ : A * A.map h.bar = μ • 1) :
    FixConclD8 h 3 A (fun M => M.map h.bar) := by
  obtain ⟨hAt, hAt'⟩ := class2_transpose h hAu hμ
  have hA0 := ne_zero_of_unitary h (by omega) hAu
  have hμμ : μ * μ = 1 := by
    have h3 : (μ * μ - 1) • A = 0 := by
      rw [sub_smul, one_smul, ← smul_smul, ← hAt', ← hAt, sub_self]
    have := (smul_eq_zero.1 h3).resolve_right hA0
    linear_combination this
  rcases mul_self_eq_one_iff.1 hμμ with hμ1 | hμ1
  · rw [hμ1] at hμ
    exact L2CompU3Conj.exists_class2_symm_D8 h h2 (le_refl 3) hAu hμ
  · rw [hμ1] at hμ
    exact class2alt_odd_D8 h (by decide) h2 A hAu hμ

theorem exists_fixed_unitary_D8 (hp : p ≠ 2) {A : GL (Fin 3) K} {φ : K ≃+* K}
    (hA : ∀ g : unitarySU p f K 3, A * glAut φ (g : GL (Fin 3) K) * A⁻¹ ∈ unitarySU p f K 3)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1)
    (hφ : φ = RingEquiv.refl K ∨ ∀ c, φ c = h.bar c)
    (hcomp : (unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA) = MonoidHom.id _) :
    ∃ c d : unitarySU p f K 3, unitaryConjHom A φ hA c = c ∧ unitaryConjHom A φ hA d = d ∧
      c ^ 2 ∉ unitaryScalars h 3 ∧ c ^ 4 = 1 ∧ d * d = 1 ∧ d * c * d = c ^ 3 := by
  have h2 := two_ne_zero_of_ne h hp
  have hφφ : φ * φ = 1 := by
    rcases hφ with rfl | hb
    · ext c
      rfl
    · ext c
      change φ (φ c) = c
      rw [hb, hb, h.bar_bar]
  obtain ⟨μ, hμ⟩ := scalar_of_comp h h2 (le_refl 3) hφφ hA hcomp
  obtain ⟨c, d, hc1, hc2, hd1, hd2, hc3, hc4, hd3, hd4, hc5, hd5⟩ :
      ∃ c d : Matrix (Fin 3) (Fin 3) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
        (d.map h.bar)ᵀ * d = 1 ∧ d.det = 1 ∧ (∀ l : K, c * c ≠ l • 1) ∧
        c * c * (c * c) = 1 ∧ d * d = 1 ∧ d * c * d = c * c * c ∧
        (A : Matrix (Fin 3) (Fin 3) K) * c.map φ = c * (A : Matrix (Fin 3) (Fin 3) K) ∧
        (A : Matrix (Fin 3) (Fin 3) K) * d.map φ = d * (A : Matrix (Fin 3) (Fin 3) K) := by
    rcases hφ with rfl | hb
    · have hmap : (A : Matrix (Fin 3) (Fin 3) K).map (RingEquiv.refl K) =
          (A : Matrix (Fin 3) (Fin 3) K) := by
        ext i j
        rfl
      rw [hmap] at hμ
      obtain ⟨c, d, hc1, hc2, hd1, hd2, hc3, hc4, hd3, hd4, hc5, hd5⟩ :=
        fixed_class1_D8 h hp h2 hAu hμ
      have hmapc : ∀ m : Matrix (Fin 3) (Fin 3) K, m.map (RingEquiv.refl K) = m := by
        intro m
        ext i j
        rfl
      refine ⟨c, d, hc1, hc2, hd1, hd2, hc3, hc4, hd3, hd4, ?_, ?_⟩
      · rw [hmapc]
        exact hc5
      · rw [hmapc]
        exact hd5
    · have hmap : (A : Matrix (Fin 3) (Fin 3) K).map φ =
          (A : Matrix (Fin 3) (Fin 3) K).map h.bar := by
        ext i j
        exact hb _
      rw [hmap] at hμ
      obtain ⟨c, d, hc1, hc2, hd1, hd2, hc3, hc4, hd3, hd4, hc5, hd5⟩ :=
        fixed_class2_D8 h h2 hAu hμ
      have hmapc : ∀ m : Matrix (Fin 3) (Fin 3) K, m.map φ = m.map h.bar := by
        intro m
        ext i j
        exact hb _
      refine ⟨c, d, hc1, hc2, hd1, hd2, hc3, hc4, hd3, hd4, ?_, ?_⟩
      · rw [hmapc]
        exact hc5
      · rw [hmapc]
        exact hd5
  have hfix : ∀ (m : Matrix (Fin 3) (Fin 3) K) (hm1 : (m.map h.bar)ᵀ * m = 1) (hm2 : m.det = 1),
      (A : Matrix (Fin 3) (Fin 3) K) * m.map φ = m * (A : Matrix (Fin 3) (Fin 3) K) →
        unitaryConjHom A φ hA (mkSU h m hm1 hm2) = mkSU h m hm1 hm2 := by
    intro m hm1 hm2 hm5
    apply Subtype.ext
    rw [coe_unitaryConjHom, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_glAut, coe_mkSU]
    exact hm5
  have hcoe := coe_mkSU h c hc1 hc2
  have hdoe := coe_mkSU h d hd1 hd2
  refine ⟨mkSU h c hc1 hc2, mkSU h d hd1 hd2, hfix c hc1 hc2 hc5, hfix d hd1 hd2 hd5, ?_, ?_, ?_,
    ?_⟩
  · intro hmem
    rw [mem_unitaryScalars] at hmem
    obtain ⟨u, -, -, hu⟩ := hmem
    apply hc3 (u : K)
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hu
    simp only [pow_two, Subgroup.coe_mul, Units.val_mul, hcoe, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at this
    rw [this, Matrix.smul_one_eq_diagonal]
  · have : (mkSU h c hc1 hc2 : unitarySU p f K 3) ^ 4 = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcoe, OneMemClass.coe_one,
        Units.val_one]
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hc4]
    exact this
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hdoe, OneMemClass.coe_one, Units.val_one]
    exact hd3
  · apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      hcoe, hdoe]
    rw [hd4]
    exact (pow_three' _).symm

end CFSG.GH74.Generic.BProg.B3.L2CompU3Fix
