module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteW
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Struct

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open Subgroup CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models Polynomial
open scoped MatrixGroups

section Field

variable {K : Type} [Field K] [Finite K]

theorem exists_quadForm_eq (hK : ringChar K ≠ 2) {τ : K} (hτ : τ ^ 2 ≠ 4) (s : K) :
    ∃ x y : K, x ^ 2 + τ * x * y + y ^ 2 = s := by
  classical
  have := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hδ : (4 - τ ^ 2 : K) ≠ 0 := fun h => hτ (by linear_combination -h)
  have hf : degree (X ^ 2 : K[X]) = 2 := degree_X_pow 2
  have hg : degree (C (4 - τ ^ 2) * X ^ 2 - C (4 * s) : K[X]) = 2 := by
    have h1 : degree (C (4 - τ ^ 2) * X ^ 2 : K[X]) = 2 := degree_C_mul_X_pow 2 hδ
    rw [degree_sub_eq_left_of_degree_lt (by rw [h1]; exact lt_of_le_of_lt degree_C_le (by decide)),
      h1]
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hK)
  simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hab
  refine ⟨(a - τ * b) / 2, b, ?_⟩
  field_simp
  linear_combination hab

theorem det_smul_one_add_smul (m : SL(2, K)) (x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (m : Matrix (Fin 2) (Fin 2) K)).det =
      x ^ 2 + (m : Matrix (Fin 2) (Fin 2) K).trace * x * y + y ^ 2 := by
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  linear_combination y ^ 2 * hdet

theorem smul_one_add_smul_mul_comm (m : Matrix (Fin 2) (Fin 2) K) (x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • m) * m = m * (x • 1 + y • m) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem sq_eq_trace_smul_sub_one (m : SL(2, K)) :
    (m : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      (m : Matrix (Fin 2) (Fin 2) K).trace • (m : Matrix (Fin 2) (Fin 2) K) - 1 := by
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination -hdet

theorem pow_eq_of_trace {m : SL(2, K)} {ε : K} (hε : ε ^ 2 = 1)
    (htr : (m : Matrix (Fin 2) (Fin 2) K).trace = 2 * ε) (k : ℕ) :
    (m : Matrix (Fin 2) (Fin 2) K) ^ (k + 1) =
      (((k + 1 : ℕ) : K) * ε ^ k) • (m : Matrix (Fin 2) (Fin 2) K) - ((k : K) * ε ^ (k + 1)) • 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsq := sq_eq_trace_smul_sub_one m
    rw [htr] at hsq
    rw [pow_succ, ih, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      ← sq, hsq]
    have hε3 : ε ^ (k + 2) = ε ^ k := by rw [pow_add, hε, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    rw [show k + 1 + 1 = k + 2 by ring, hε3, pow_succ ε k]
    ring

theorem trace_sq_ne_four_of_orderOf {m : SL(2, K)} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ ringChar K) (hm : orderOf m = r) :
    (m : Matrix (Fin 2) (Fin 2) K).trace ^ 2 ≠ 4 := by
  intro h4
  have hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  set p := ringChar K with hpdef
  have hfac : ((m : Matrix (Fin 2) (Fin 2) K).trace - 2) *
      ((m : Matrix (Fin 2) (Fin 2) K).trace + 2) = 0 := by linear_combination h4
  obtain ⟨ε, hε, htr⟩ : ∃ ε : K, ε ^ 2 = 1 ∧ (m : Matrix (Fin 2) (Fin 2) K).trace = 2 * ε := by
    rcases mul_eq_zero.1 hfac with h | h
    · exact ⟨1, by ring, by linear_combination h⟩
    · exact ⟨-1, by ring, by linear_combination h⟩
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpow := pow_eq_of_trace hε htr (p - 1)
  rw [Nat.sub_add_cancel hp1] at hpow
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hpm1 : ((p - 1 : ℕ) : K) = -1 := by
    rw [Nat.cast_sub hp1, hpK, Nat.cast_one, zero_sub]
  have hpow' : (m : Matrix (Fin 2) (Fin 2) K) ^ p = ε ^ p • 1 := by
    rw [hpow, hpK, zero_mul, zero_smul, zero_sub, hpm1, neg_one_mul, neg_smul, neg_neg]
  have h2p : m ^ (2 * p) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_mul', hpow', _root_.smul_pow, one_pow, ← pow_mul,
      mul_comm p 2, pow_mul, hε, one_pow, one_smul, Matrix.SpecialLinearGroup.coe_one]
  have hdvd : r ∣ 2 * p := hm ▸ orderOf_dvd_of_pow_eq_one h2p
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
  · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp.out).1 h)

theorem exists_orderOf_eq_prime_SL2 {r : ℕ} [Fact r.Prime]
    (hr : r ∣ Nat.card K ^ 2 - 1) : ∃ m : SL(2, K), orderOf m = r := by
  classical
  have := Fintype.ofFinite K
  have hcard : Nat.card (SL(2, K)) = (Nat.card K ^ 2 - 1) * Nat.card K := by
    rw [Matrix.card_SL_field, Nat.card_eq_fintype_card, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
    have : Fintype.card K ^ 2 - Fintype.card K = Fintype.card K * (Fintype.card K - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [this, ← mul_assoc, Nat.mul_div_assoc _ (dvd_refl _), Nat.div_self (by
      have : 2 ≤ Fintype.card K := Fintype.one_lt_card
      omega), mul_one]
  have := Finite.of_fintype (SL(2, K))
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' (G := SL(2, K)) r
    (by rw [hcard]; exact dvd_mul_of_dvd_left hr _)
  exact ⟨m, hm⟩

end Field

section Torus


variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem exists_mul_slB_commute (hK : ringChar K ≠ 2) {t : twistedGroup σ} (ht : t ∈ TK σ)
    {m : SL(2, K)} (htr : (m : Matrix (Fin 2) (Fin 2) K).trace ^ 2 ≠ 4) :
    ∃ B : SL(2, K), t * slB σ hσ B * slB σ hσ m = slB σ hσ m * (t * slB σ hσ B) := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, -, hs⟩ := torus_conj_slB hσ hb
  obtain ⟨x, y, hxy⟩ := exists_quadForm_eq hK htr (s : K)
  set z : Matrix (Fin 2) (Fin 2) K := x • 1 + y • (m : Matrix (Fin 2) (Fin 2) K) with hz
  have hzdet : z.det = s := by rw [hz, det_smul_one_add_smul, hxy]
  set B : SL(2, K) := ⟨!![((s⁻¹ : Kˣ) : K), 0; 0, 1] * z, by
    rw [Matrix.det_mul, hzdet, Matrix.det_fin_two_of]
    simp⟩ with hB
  have hDB : ((diagGL s * Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = z := by
    rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hB]
    show !![(s : K), 0; 0, 1] * (!![((s⁻¹ : Kˣ) : K), 0; 0, 1] * z) = z
    rw [← Matrix.mul_assoc]
    have : !![(s : K), 0; 0, 1] * !![((s⁻¹ : Kˣ) : K), 0; 0, 1] = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [this, Matrix.one_mul]
  have hfix : glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL B) m = m := by
    apply Subtype.ext
    rw [glConjSL_coe, hDB]
    have hcomm := smul_one_add_smul_mul_comm (m : Matrix (Fin 2) (Fin 2) K) x y
    rw [← hz] at hcomm
    rw [hcomm, Matrix.mul_assoc]
    have hinv : z * (((diagGL s * Matrix.SpecialLinearGroup.toGL B)⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← hDB]; exact gl_mul_inv _
    rw [hinv, Matrix.mul_one]
  have hconj : (t * slB σ hσ B) * slB σ hσ m * (t * slB σ hσ B)⁻¹ = slB σ hσ m := by
    calc (t * slB σ hσ B) * slB σ hσ m * (t * slB σ hσ B)⁻¹
        = t * slB σ hσ (B * m * B⁻¹) * t⁻¹ := by simp only [map_mul, map_inv]; group
      _ = slB σ hσ (glConjSL (diagGL s) (B * m * B⁻¹)) := hs _
      _ = slB σ hσ (glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL B) m) := by
          rw [glConjSL_mul, glConjSL_toGL]
      _ = slB σ hσ m := by rw [hfix]
  refine ⟨B, ?_⟩
  calc t * slB σ hσ B * slB σ hσ m
      = (t * slB σ hσ B) * slB σ hσ m * (t * slB σ hσ B)⁻¹ * (t * slB σ hσ B) := by group
    _ = slB σ hσ m * (t * slB σ hσ B) := by rw [hconj]

include hσ in
theorem SProd_le_of_invCentGroup_le (hK : ringChar K ≠ 2) {H : Subgroup (twistedGroup σ)}
    (hM : invCentGroup σ hσ ≤ H) {m : SL(2, K)}
    (htr : (m : Matrix (Fin 2) (Fin 2) K).trace ^ 2 ≠ 4)
    (hC : Subgroup.centralizer ({slB σ hσ m} : Set (twistedGroup σ)) ≤ H) :
    SProd σ hσ ≤ H := by
  have hA : ∀ A, slLong σ hσ A ∈ H := fun A => hM (mem_sup_left ⟨A, rfl⟩)
  have hB : ∀ B, slB σ hσ B ∈ H := fun B => hM (mem_sup_right ⟨B, rfl⟩)
  rintro _ ⟨t, ht, A, B, rfl⟩
  obtain ⟨B', hB'⟩ := exists_mul_slB_commute hσ hK ht htr
  have htB : t * slB σ hσ B' ∈ H :=
    hC (Subgroup.mem_centralizer_singleton_iff.2 hB')
  have ht' : t ∈ H := by
    have := mul_mem htB (inv_mem (hB B'))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mul_mem ht' (hA A)) (hB B)

end Torus

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
