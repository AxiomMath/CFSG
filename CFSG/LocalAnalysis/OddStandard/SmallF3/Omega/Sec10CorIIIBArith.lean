module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf

private lemma one_le_mul_sub_one_div_two {n : ℕ} (hn : 2 ≤ n) : 1 ≤ n * (n - 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  calc 1 * 2 = 2 * 1 := by norm_num
    _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)

private lemma one_le_sq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ n ^ 2 := by
  calc 1 ≤ 2 ^ 2 := by norm_num
    _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2

private lemma one_le_mul_sub_one {n : ℕ} (hn : 3 ≤ n) : 1 ≤ n * (n - 1) := by
  calc 1 ≤ 3 * (3 - 1) := by norm_num
    _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)

private lemma c3b_self_le_mul {N f : ℕ} (hf : 1 ≤ f) : N ≤ N * f := by
  calc N = N * 1 := (mul_one N).symm
    _ ≤ N * f := Nat.mul_le_mul (le_refl N) hf

theorem c3b_prime_eq_of_dvd {p a b c d e g : ℕ} (hp : p.Prime)
    (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 13 ^ e * 41 ^ g) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 41 := by
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  have h41 : Nat.Prime 41 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp h2).mp (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp h3).mp (hp.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inl
            ((Nat.prime_dvd_prime_iff_eq hp h5).mp (hp.dvd_of_dvd_pow h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp h7).mp (hp.dvd_of_dvd_pow h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hp h13).mp (hp.dvd_of_dvd_pow h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp h41).mp (hp.dvd_of_dvd_pow h))))))

theorem c3b_eq_psl_two_of_exponent_le_two {τ : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : lieSylowExponent τ n * f ≤ 2) : τ = .PSL ∧ n = 2 ∧ f ≤ 2 := by
  obtain ⟨hp, hf, hτ⟩ := hadm
  cases τ <;> dsimp only [StatedLieAdmissible] at hτ <;> simp only [lieSylowExponent] at h
  ·
    have hn2 : n = 2 := by
      by_contra hn
      have h3 : 3 ≤ n := by omega
      have hN : 3 ≤ n * (n - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        exact Nat.mul_le_mul h3 (show 2 ≤ n - 1 by omega)
      have hNf := c3b_self_le_mul (N := n * (n - 1) / 2) hf
      omega
    refine ⟨rfl, hn2, ?_⟩
    rw [hn2] at h
    norm_num at h
    exact h
  ·
    exfalso
    have hN : 3 ≤ n * (n - 1) / 2 := by
      have h3 : 3 ≤ n := hτ.1
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      exact Nat.mul_le_mul h3 (show 2 ≤ n - 1 by omega)
    have hNf := c3b_self_le_mul (N := n * (n - 1) / 2) hf
    omega
  ·
    exfalso
    have hN : 3 ≤ n ^ 2 := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hτ.1 2
    have hNf := c3b_self_le_mul (N := n ^ 2) hf
    omega
  ·
    exfalso
    have hn2 : 2 ≤ n := by omega
    have hN : 3 ≤ n ^ 2 := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn2 2
    have hNf := c3b_self_le_mul (N := n ^ 2) hf
    omega
  ·
    exfalso
    have hN : 3 ≤ n * (n - 1) := by
      calc 3 ≤ 4 * (4 - 1) := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hτ (show 3 ≤ n - 1 by omega)
    have hNf := c3b_self_le_mul (N := n * (n - 1)) hf
    omega
  ·
    exfalso
    have hN : 3 ≤ n * (n - 1) := by
      calc 3 ≤ 4 * (4 - 1) := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hτ (show 3 ≤ n - 1 by omega)
    have hNf := c3b_self_le_mul (N := n * (n - 1)) hf
    omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; exact absurd hτ.2.1 hp2
  · exfalso; exact absurd hτ.2.1 hp3
  · exfalso; exact absurd hτ.2.1 hp2
  · exfalso; exact absurd hτ.2.1 hp2

theorem c3b_one_le_lieSylowExponent {τ : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible τ n p f) : 1 ≤ lieSylowExponent τ n := by
  obtain ⟨hp, hf, hτ⟩ := hadm
  cases τ <;> dsimp only [StatedLieAdmissible] at hτ <;> simp only [lieSylowExponent]
  · exact one_le_mul_sub_one_div_two hτ.1
  · exact one_le_mul_sub_one_div_two (by omega)
  · exact one_le_sq hτ.1
  · exact one_le_sq (by omega)
  · exact one_le_mul_sub_one (by omega)
  · exact one_le_mul_sub_one (by omega)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

theorem c3b_exponent_le_two {p k c : ℕ} (hp : p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 41)
    (hc : c = 25920 ∨ c = 6065280 ∨ c = 3265920 ∨ c = 4585351680 ∨ c = 4952179814400 ∨
      c = 10151968619520) (h : p ^ k ∣ c) : k ≤ 2 := by
  by_contra hk
  have hk3 : 3 ≤ k := by omega
  have h3 : p ^ 3 ∣ c := (Nat.pow_dvd_pow p hk3).trans h
  rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num at h3

theorem c3b_false_of_fOrder {τ : StatedLieTag} {n p f c : ℕ} (hadm : StatedLieAdmissible τ n p f)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hmul : c * lieOrderDivisor τ n (p ^ f) = lieOrderNumerator τ n (p ^ f))
    (hfac : c.factorization p = lieSylowExponent τ n * f)
    (hc : c = 25920 ∨ c = 6065280 ∨ c = 3265920 ∨ c = 4585351680 ∨ c = 4952179814400 ∨
      c = 10151968619520) : False := by
  have hN : 1 ≤ lieSylowExponent τ n := c3b_one_le_lieSylowExponent hadm
  have hf : 1 ≤ f := hadm.2.1
  have hpk : p ^ (lieSylowExponent τ n * f) ∣ c := by
    have h1 : p ^ c.factorization p ∣ c := Nat.ordProj_dvd c p
    rwa [hfac] at h1
  have hp_dvd_c : p ∣ c := by
    have h1 : p ^ 1 ∣ p ^ (lieSylowExponent τ n * f) :=
      Nat.pow_dvd_pow p (Nat.succ_le_of_lt (Nat.mul_pos hN hf))
    simpa using h1.trans hpk
  have hp_odd : p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 41 := by
    have hp_primes : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 41 := by
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · have h' : (2 : ℕ) ^ 6 * 3 ^ 4 * 5 ^ 1 * 7 ^ 0 * 13 ^ 0 * 41 ^ 0 =
            25920 := by norm_num
        rw [← h'] at hp_dvd_c
        exact c3b_prime_eq_of_dvd hadm.1 hp_dvd_c
      · have h' : (2 : ℕ) ^ 7 * 3 ^ 6 * 5 ^ 1 * 7 ^ 0 * 13 ^ 1 * 41 ^ 0 =
            6065280 := by norm_num
        rw [← h'] at hp_dvd_c
        exact c3b_prime_eq_of_dvd hadm.1 hp_dvd_c
      · have h' : (2 : ℕ) ^ 7 * 3 ^ 6 * 5 ^ 1 * 7 ^ 1 * 13 ^ 0 * 41 ^ 0 =
            3265920 := by norm_num
        rw [← h'] at hp_dvd_c
        exact c3b_prime_eq_of_dvd hadm.1 hp_dvd_c
      · have h' : (2 : ℕ) ^ 9 * 3 ^ 9 * 5 ^ 1 * 7 ^ 1 * 13 ^ 1 * 41 ^ 0 =
            4585351680 := by norm_num
        rw [← h'] at hp_dvd_c
        exact c3b_prime_eq_of_dvd hadm.1 hp_dvd_c
      · have h' : (2 : ℕ) ^ 12 * 3 ^ 12 * 5 ^ 2 * 7 ^ 1 * 13 ^ 1 * 41 ^ 0 =
            4952179814400 := by norm_num
        rw [← h'] at hp_dvd_c
        exact c3b_prime_eq_of_dvd hadm.1 hp_dvd_c
      · have h' : (2 : ℕ) ^ 10 * 3 ^ 12 * 5 ^ 1 * 7 ^ 1 * 13 ^ 1 * 41 ^ 1 =
            10151968619520 := by norm_num
        rw [← h'] at hp_dvd_c
        exact c3b_prime_eq_of_dvd hadm.1 hp_dvd_c
    rcases hp_primes with h | h | h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hNf_le_two : lieSylowExponent τ n * f ≤ 2 := c3b_exponent_le_two hp_odd hc hpk
  obtain ⟨hτPSL, hn2, hf2⟩ := c3b_eq_psl_two_of_exponent_le_two hadm hp2 hp3 hNf_le_two
  subst hτPSL
  subst hn2
  rw [lieOrderDivisor, lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton] at hmul
  interval_cases f <;>
    rcases hp_odd with rfl | rfl | rfl | rfl <;>
    norm_num at hmul <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    omega

end CFSG.OddStandard.SmallF3.Omega
