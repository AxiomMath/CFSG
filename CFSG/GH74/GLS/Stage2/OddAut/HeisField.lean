module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K]

theorem exists_frobenius_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (τ : K ≃+* K) : ∃ k : ℕ, k < f ∧ ∀ a : K, τ a = a ^ (p ^ k) := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hτ : τ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top τ
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have hf0 : (f : ℤ) ≠ 0 := by exact_mod_cast (by omega : f ≠ 0)
  refine ⟨(m % (f : ℤ)).toNat, ?_, ?_⟩
  · have h1 : m % (f : ℤ) < f := Int.emod_lt_of_pos m (by exact_mod_cast hf)
    have h2 : 0 ≤ m % (f : ℤ) := Int.emod_nonneg m hf0
    omega
  · have hpow : ∀ (n : ℕ) (a : K), (φ ^ n) a = a ^ (p ^ n) := by
      intro n
      induction n with
      | zero => intro a; simp
      | succ n ih =>
        intro a
        rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, pow_succ]
    have h3 : φ ^ m = φ ^ ((m % (f : ℤ)).toNat) := by
      have := zpow_mod_orderOf φ m
      rw [hord] at this
      rw [← this]
      have h2 : 0 ≤ m % (f : ℤ) := Int.emod_nonneg m hf0
      rw [← zpow_natCast, Int.toNat_of_nonneg h2]
    intro a
    rw [h3, hpow]

end CFSG.GH74.GLS.Stage2.OddAut

namespace CFSG.GH74.GLS.Stage2.OddAut

open Matrix

variable {K : Type} [Field K]

theorem trace_argument (h2K : (2 : K) ≠ 0) (τ : K ≃+* K) {s : K} (hs : s ≠ 0) (X : GL (Fin 3) K) (lam : K)
    (h : (X : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![τ s ^ 3, (τ s ^ 3)⁻¹, 1] * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lam • diagonal ![s ^ 3, (s ^ 3)⁻¹, 1]) :
    s ^ 6 + s ^ 3 + 1 = 0 ∨ τ s ^ 3 = s ^ 3 ∨ τ s ^ 3 * s ^ 3 = 1 := by
  set a : K := τ s ^ 3 with ha
  set u : K := s ^ 3 with hu
  have hu0 : u ≠ 0 := pow_ne_zero 3 hs
  have ha0 : a ≠ 0 := pow_ne_zero 3 ((map_ne_zero τ).mpr hs)
  set Da : Matrix (Fin 3) (Fin 3) K := diagonal ![a, a⁻¹, 1] with hDa
  set Du : Matrix (Fin 3) (Fin 3) K := diagonal ![u, u⁻¹, 1] with hDu
  have hdet : lam ^ 3 = 1 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, hDu] at this
    have hX : (X : Matrix (Fin 3) (Fin 3) K).det * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    simp only [hDa, det_diagonal, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fintype.card_fin] at this
    have e1 : a * a⁻¹ * 1 = 1 := by rw [mul_inv_cancel₀ ha0, mul_one]
    have e2 : u * u⁻¹ * 1 = 1 := by rw [mul_inv_cancel₀ hu0, mul_one]
    calc lam ^ 3 = lam ^ 3 * (u * u⁻¹ * 1) := by rw [e2, mul_one]
      _ = (X : Matrix (Fin 3) (Fin 3) K).det * (a * a⁻¹ * 1) *
          ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := this.symm
      _ = 1 := by rw [e1, mul_one, hX]
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hdet
  have htr1 : a + a⁻¹ + 1 = lam * (u + u⁻¹ + 1) := by
    have := congrArg Matrix.trace h
    rw [Matrix.trace_units_conj, Matrix.trace_smul] at this
    simpa [hDa, hDu, Matrix.trace_diagonal, Fin.sum_univ_three, add_assoc] using this
  have hsq : ((X : Matrix (Fin 3) (Fin 3) K) * Da * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 2 =
      (X : Matrix (Fin 3) (Fin 3) K) * Da ^ 2 * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have hXi : ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (X : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc _ = (X : Matrix (Fin 3) (Fin 3) K) * Da * (((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (X : Matrix (Fin 3) (Fin 3) K)) * Da * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [pow_two]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hXi, pow_two]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  have htr2 : a ^ 2 + (a⁻¹) ^ 2 + 1 = lam ^ 2 * (u ^ 2 + (u⁻¹) ^ 2 + 1) := by
    have h' : ((X : Matrix (Fin 3) (Fin 3) K) * Da * ((X⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 2 =
        (lam • Du) ^ 2 := by rw [h]
    rw [hsq] at h'
    have := congrArg Matrix.trace h'
    rw [Matrix.trace_units_conj, smul_pow, Matrix.trace_smul] at this
    simpa [hDa, hDu, pow_two, Matrix.trace_diagonal, Fin.sum_univ_three, add_assoc, diagonal_mul_diagonal] using this
  have haa : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
  have huu : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
  set α : K := a + a⁻¹ with hα
  set μ : K := u + u⁻¹ with hμ
  have e1 : α + 1 = lam * (μ + 1) := by rw [hα, hμ]; linear_combination htr1
  have e2 : α ^ 2 - 1 = lam ^ 2 * (μ ^ 2 - 1) := by
    have h1 : a ^ 2 + (a⁻¹) ^ 2 = α ^ 2 - 2 := by
      rw [hα]; linear_combination (-2 : K) * haa
    have h2 : u ^ 2 + (u⁻¹) ^ 2 = μ ^ 2 - 2 := by
      rw [hμ]; linear_combination (-2 : K) * huu
    rw [h1, h2] at htr2
    linear_combination htr2
  have key : lam * (μ + 1) * ((α - 1) - lam * (μ - 1)) = 0 := by
    linear_combination e2 - (α - 1) * e1
  rcases mul_eq_zero.mp key with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hlam0
    · left
      have h5 : u ^ 2 + u + 1 = (μ + 1) * u := by
        rw [hμ]; linear_combination (-1 : K) * huu
      rw [h2, zero_mul] at h5
      calc s ^ 6 + s ^ 3 + 1 = u ^ 2 + u + 1 := by rw [hu]; ring
        _ = 0 := h5
  · right
    have hlam1 : lam = 1 := by
      have h3 : 2 * (1 - lam) = 0 := by linear_combination e1 - h1
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h h2K
      · linear_combination -h
    rw [hlam1] at e1
    have hαμ : α = μ := by linear_combination e1
    have h4 : (a - u) * (a * u - 1) = a * u * (α - μ) := by
      rw [hα, hμ]; linear_combination (-u) * haa + a * huu
    rw [hαμ, sub_self, mul_zero] at h4
    rcases mul_eq_zero.mp h4 with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact sub_eq_zero.mp h

end CFSG.GH74.GLS.Stage2.OddAut

namespace CFSG.GH74.GLS.Stage2.OddAut

variable {K : Type} [Field K]

theorem generator_contradiction {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (τ : K ≃+* K) (hτ : τ ≠ 1) {g : K} (hg0 : g ≠ 0)
    (hgord : ∀ n : ℕ, g ^ n = 1 → p ^ f - 1 ∣ n) :
    ¬ (g ^ 6 + g ^ 3 + 1 = 0 ∨ τ g ^ 3 = g ^ 3 ∨ τ g ^ 3 * g ^ 3 = 1) := by
  obtain ⟨k, hkf, hτk⟩ := exists_frobenius_pow hp hf hK τ
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hτ
    ext a
    rw [hτk, pow_zero, pow_one]
    rfl
  have hP5 : 5 ≤ p ^ k := calc 5 ≤ p := hp5
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos (Nat.one_le_iff_ne_zero.mpr hk0)
  have hpf : 5 * p ^ k ≤ p ^ f := calc 5 * p ^ k ≤ p * p ^ k := Nat.mul_le_mul_right _ hp5
    _ = p ^ (k + 1) := by rw [pow_succ, mul_comm]
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hkf
  have hf2 : 25 ≤ p ^ f := by
    have : 5 * 5 ≤ 5 * p ^ k := Nat.mul_le_mul_left 5 hP5
    omega
  have hτg : τ g = g ^ (p ^ k) := hτk g
  rintro (h | h | h)
  · have h9 : g ^ 9 = 1 := by linear_combination (g ^ 3 - 1) * h
    have := Nat.le_of_dvd (by norm_num) (hgord 9 h9)
    omega
  · have h1 : g ^ (3 * p ^ k) = g ^ 3 := by
      rw [← h, hτg, ← pow_mul, mul_comm]
    have h2 : g ^ (3 * p ^ k - 3) = 1 := by
      rw [pow_sub₀ _ hg0 (by omega), h1, mul_inv_cancel₀ (pow_ne_zero 3 hg0)]
    have := Nat.le_of_dvd (by omega) (hgord _ h2)
    omega
  · have h1 : g ^ (3 * p ^ k + 3) = 1 := by
      rw [pow_add, ← h, hτg, ← pow_mul, mul_comm (p ^ k) 3]
    have := Nat.le_of_dvd (by omega) (hgord _ h1)
    omega

end CFSG.GH74.GLS.Stage2.OddAut
