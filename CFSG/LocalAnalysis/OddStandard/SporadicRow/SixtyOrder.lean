module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Assembly.LowTwoRank CatLeaf

private theorem eq_psl_two_of_lieSylowExponent_eq_one {τ : StatedLieTag} {n p f : ℕ}
    (ha : StatedLieAdmissible τ n p f) (h : lieSylowExponent τ n = 1) :
    τ = .PSL ∧ n = 2 := by
  obtain ⟨-, -, ha'⟩ := ha
  cases τ
  · refine ⟨rfl, ?_⟩
    by_contra hn
    have hn3 : 3 ≤ n := by omega
    have := tri_three hn3
    simp only [lieSylowExponent] at h
    omega
  · exfalso
    have := tri_three ha'.1
    simp only [lieSylowExponent] at h
    omega
  · exfalso
    have := ha'.1
    simp only [lieSylowExponent] at h
    nlinarith
  · exfalso
    have := ha'.1
    simp only [lieSylowExponent] at h
    nlinarith
  · exfalso
    have := rect_bounds' ha'
    simp only [lieSylowExponent] at h
    omega
  · exfalso
    have := rect_bounds' ha'
    simp only [lieSylowExponent] at h
    omega
  all_goals (exfalso; simp only [lieSylowExponent] at h; omega)

theorem OddLieOrder.eq_sixty_of_dvd {m a : ℕ} (h : OddLieOrder m) (hd : m ∣ 2 ^ a * 15) :
    m = 60 := by
  obtain ⟨τ, n, p, f, hp, hp2, ha, hnum, hfac⟩ := h
  have hf1 : 1 ≤ f := ha.2.1
  have hN1 : 1 ≤ lieSylowExponent τ n := (lieSylowExponent_bounds ha).1
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.zero_dvd] at hd
    have : 0 < 2 ^ a * 15 := by positivity
    omega
  have hpow : p ^ (lieSylowExponent τ n * f) ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm0).2 (le_of_eq hfac.symm)
  have hpow15 : p ^ (lieSylowExponent τ n * f) ∣ 2 ^ a * 15 := hpow.trans hd
  have hcop : Nat.Coprime (p ^ (lieSylowExponent τ n * f)) (2 ^ a) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdiv15 : p ^ (lieSylowExponent τ n * f) ∣ 15 := hcop.dvd_of_dvd_mul_left hpow15
  have hNf1 : lieSylowExponent τ n * f = 1 := by
    have hpos : 0 < lieSylowExponent τ n * f := Nat.mul_pos (by omega) (by omega)
    have hnot : ¬ 2 ≤ lieSylowExponent τ n * f := by
      intro h2le
      have hsq : p ^ 2 ∣ p ^ (lieSylowExponent τ n * f) := pow_dvd_pow p h2le
      have hsq15 : p ^ 2 ∣ 15 := hsq.trans hdiv15
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hle : p ^ 2 ≤ 15 := Nat.le_of_dvd (by norm_num) hsq15
      have hp_eq : p = 3 := by
        by_contra hne
        have : 4 ≤ p := by omega
        nlinarith
      subst hp_eq
      norm_num at hsq15
    omega
  have hNeq : lieSylowExponent τ n = 1 := by
    have hle : lieSylowExponent τ n ≤ 1 := by
      calc lieSylowExponent τ n = lieSylowExponent τ n * 1 := (Nat.mul_one _).symm
        _ ≤ lieSylowExponent τ n * f := Nat.mul_le_mul_left _ hf1
        _ = 1 := hNf1
    omega
  have hfeq : f = 1 := by
    have hle : f ≤ 1 := by
      calc f = 1 * f := (Nat.one_mul f).symm
        _ ≤ lieSylowExponent τ n * f := Nat.mul_le_mul_right _ hN1
        _ = 1 := hNf1
    omega
  obtain ⟨hτ, hn⟩ := eq_psl_two_of_lieSylowExponent_eq_one ha hNeq
  subst hτ
  subst hn
  subst hfeq
  have hp_ne3 : p ≠ 3 := by
    intro hp3
    exact ha.2.2.2.2 (by rw [hp3]; norm_num)
  have hp_dvd15 : p ∣ 15 := by
    simpa [lieSylowExponent] using hdiv15
  have hp_eq5 : p = 5 := by
    have hp35 : p ∣ 3 * 5 := by rwa [show 3 * 5 = 15 by norm_num]
    rcases (hp.dvd_mul).1 hp35 with h3 | h5
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3) hp_ne3
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
  subst hp_eq5
  simp only [lieOrderDivisor, lieOrderNumerator] at hnum
  norm_num [Finset.Icc_self] at hnum
  omega

theorem not_oddLieOrder_of_dvd_two_pow_mul_three {m a : ℕ} (hd : m ∣ 2 ^ a * 3) :
    ¬ OddLieOrder m := by
  intro h
  have h60 : m = 60 :=
    OddLieOrder.eq_sixty_of_dvd h (hd.trans (Nat.mul_dvd_mul_left _ (by norm_num : 3 ∣ 15)))
  rw [h60] at hd
  have h5dvd : 5 ∣ 2 ^ a * 3 := (by norm_num : 5 ∣ 60).trans hd
  rcases (Nat.prime_five.dvd_mul).1 h5dvd with h52 | h53
  · exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h52)) (by norm_num)
  · norm_num at h53

end CFSG.ComponentClassification.HarrisLit.T1.SporRow