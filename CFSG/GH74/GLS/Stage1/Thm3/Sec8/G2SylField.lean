module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

theorem two_pow_mul_odd_factorization {m : ℕ} (hm : Odd m) (n : ℕ) :
    (2 ^ n * m).factorization 2 = n := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (by positivity) hm0]
  simp [Nat.Prime.factorization_pow Nat.prime_two]
  exact Nat.factorization_eq_zero_of_not_dvd (by
    rintro ⟨c, hc⟩; obtain ⟨k, hk⟩ := hm; omega)

theorem exists_split_data (K : Type) [Field K] [Finite K] (hK : Nat.card K % 4 = 1) :
    ∃ (n : ℕ) (ζ : Kˣ), (Nat.card K - 1).factorization 2 = n ∧ 2 ≤ n ∧ ζ ^ (2 ^ n) = 1 ∧
      ζ ^ (2 ^ (n - 1)) = -1 ∧ ∀ p : K, (ζ : K) ≠ p * p := by
  have := Fintype.ofFinite K
  have hq : Fintype.card K % 4 = 1 := by rwa [← Nat.card_eq_fintype_card]
  have hch : ringChar K ≠ 2 := by
    intro h
    have := FiniteField.even_card_of_char_two h
    omega
  have hone : 1 < Fintype.card K := Fintype.one_lt_card
  have hne : Fintype.card K - 1 ≠ 0 := by omega
  obtain ⟨n, m, hm, hqm⟩ := Nat.exists_eq_two_pow_mul_odd hne
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> obtain ⟨k, hk⟩ := hm <;> omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgord : orderOf g = 2 ^ n * m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, ← hqm]
    rw [Nat.card_eq_fintype_card]
  have hm0 : 0 < m := by obtain ⟨k, hk⟩ := hm; omega
  have hζord : orderOf (g ^ m) = 2 ^ n := by
    rw [orderOf_pow' g hm0.ne', hgord]
    have : Nat.gcd (2 ^ n * m) m = m := Nat.gcd_eq_right (Dvd.intro_left _ rfl)
    rw [this, Nat.mul_div_cancel _ hm0]
  refine ⟨n, g ^ m, ?_, hn2, ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, hqm, two_pow_mul_odd_factorization hm]
  · rw [← hζord]; exact pow_orderOf_eq_one _
  · have h1 : ((g ^ m) ^ (2 ^ (n - 1))) * ((g ^ m) ^ (2 ^ (n - 1))) = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']
      rw [show n - 1 + 1 = n by omega, ← hζord]; exact pow_orderOf_eq_one _
    have h2 : ((g ^ m) ^ (2 ^ (n - 1))) ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hζord] at this
      have h3 : 2 ^ n ≤ 2 ^ (n - 1) := Nat.le_of_dvd (by positivity) this
      have : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have h4 : (((g ^ m) ^ (2 ^ (n - 1)) : Kˣ) : K) = 1 ∨
        (((g ^ m) ^ (2 ^ (n - 1)) : Kˣ) : K) = -1 := by
      apply mul_self_eq_one_iff.1
      have := congrArg Units.val h1
      simpa using this
    rcases h4 with h4 | h4
    · exact absurd (Units.ext h4) h2
    · exact Units.ext (by simpa using h4)
  · intro p hp
    have hp0 : p ≠ 0 := by
      rintro rfl
      simp at hp
    have hsq : IsSquare (g ^ m : Kˣ) := ⟨Units.mk0 p hp0, Units.ext (by simpa using hp)⟩
    rw [FiniteField.unit_isSquare_iff hch] at hsq
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hdiv : Fintype.card K / 2 = 2 ^ (n - 1) * m := by
      have h5 : Fintype.card K - 1 = 2 * (2 ^ (n - 1) * m) := by rw [hqm, h2n, mul_assoc]
      omega
    have hmin : (g ^ m) ^ (2 ^ (n - 1)) = -1 := by
      have h1 : ((g ^ m) ^ (2 ^ (n - 1))) * ((g ^ m) ^ (2 ^ (n - 1))) = 1 := by
        rw [← pow_add, ← two_mul, ← pow_succ']
        rw [show n - 1 + 1 = n by omega, ← hζord]; exact pow_orderOf_eq_one _
      have h2 : ((g ^ m) ^ (2 ^ (n - 1))) ≠ 1 := by
        intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hζord] at this
        have h3 : 2 ^ n ≤ 2 ^ (n - 1) := Nat.le_of_dvd (by positivity) this
        have : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have h4 : (((g ^ m) ^ (2 ^ (n - 1)) : Kˣ) : K) = 1 ∨
          (((g ^ m) ^ (2 ^ (n - 1)) : Kˣ) : K) = -1 := by
        apply mul_self_eq_one_iff.1
        have := congrArg Units.val h1
        simpa using this
      rcases h4 with h4 | h4
      · exact absurd (Units.ext h4) h2
      · exact Units.ext (by simpa using h4)
    rw [hdiv, pow_mul, hmin, Odd.neg_one_pow hm] at hsq
    have : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := congrArg Units.val hsq
    simp only [Units.val_neg, Units.val_one] at this
    exact Ring.neg_one_ne_one_of_char_ne_two hch this


section Arith

theorem factorization_sq_sub_one {q : ℕ} (hq1 : 1 < q) :
    (q ^ 2 - 1).factorization 2 = (q - 1).factorization 2 + (q + 1).factorization 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h1 : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
  have h2 : (r + 1) ^ 2 - 1 = r * (r + 2) := by omega
  rw [h2, Nat.factorization_mul (by omega) (by omega)]
  simp

theorem factorization_add_one_of_mod_four_eq_one {q : ℕ} (h : q % 4 = 1) :
    (q + 1).factorization 2 = 1 := by
  have : q + 1 = 2 ^ 1 * ((q + 1) / 2) := by omega
  rw [this, two_pow_mul_odd_factorization (Nat.odd_iff.2 (by omega))]

theorem factorization_sub_one_of_mod_four_eq_three {q : ℕ} (h : q % 4 = 3) :
    (q - 1).factorization 2 = 1 := by
  have : q - 1 = 2 ^ 1 * ((q - 1) / 2) := by omega
  rw [this, two_pow_mul_odd_factorization (Nat.odd_iff.2 (by omega))]

end Arith

theorem factorization_ordG2 {q : ℕ} (hq : q % 2 = 1) (hq1 : 1 < q) :
    (q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)).factorization 2 = 2 * (q ^ 2 - 1).factorization 2 := by
  have hqo : Odd q := Nat.odd_iff.2 hq
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h6 : q ^ 6 - 1 = (q ^ 2 - 1) * (q ^ 4 + q ^ 2 + 1) := by
    zify [h1, h2]
    ring
  have hodd1 : Odd (q ^ 4 + q ^ 2 + 1) := ((hqo.pow).add_odd (hqo.pow)).add_one
  have hne1 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hne2 : q ^ 4 + q ^ 2 + 1 ≠ 0 := by omega
  have hne3 : q ^ 6 - 1 ≠ 0 := by rw [h6]; exact mul_ne_zero hne1 hne2
  have hne4 : q ^ 6 ≠ 0 := by positivity
  have hv2 : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      have := Nat.odd_iff.1 hqo
      omega)
  have hvodd : (q ^ 4 + q ^ 2 + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      obtain ⟨k, hk⟩ := hodd1
      obtain ⟨c, hc⟩ := hd
      omega)
  rw [Nat.factorization_mul (mul_ne_zero hne4 hne3) hne1, Nat.factorization_mul hne4 hne3, h6,
    Nat.factorization_mul hne1 hne2]
  simp [hv2, hvodd]
  ring


end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
