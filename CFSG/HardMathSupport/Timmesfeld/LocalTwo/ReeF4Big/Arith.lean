module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux.Arith
public import Mathlib.Data.Nat.GCD.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

theorem dvd_cases_of_dvd_pow_four_sub_one {a p : ℕ} (hp : p.Prime)
    (h : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1) :
    p ∣ 2 ^ (2 * a + 1) - 1 ∨ p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have key : ∀ Q : ℕ, 1 ≤ Q → Q ^ 4 - 1 = (Q - 1) * ((Q + 1) * (Q ^ 2 + 1)) := by
    intro Q hQ
    have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
    zify [hQ, h4]
    ring
  have hQ1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [key _ hQ1] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · exact Or.inl h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

theorem not_dvd_orderF_aux {x r : ℕ} (hx2 : 2 ≤ x) (hxe : 2 ∣ x) (hx3 : x % 3 = 2)
    (hr : r.Prime) (hr2 : r ≠ 2) (hdvd : x ^ r - 1 ∣ orderF x) : False := by
  by_cases hr3 : r = 3
  ·
    subst hr3
    have hs3 : x ^ 2 + x + 1 ∣ x ^ 3 - 1 := by
      have h3 : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by
        obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        zify [Nat.one_le_pow 3 (y + 1) (by omega)]
        ring
      rw [h3]
      exact Dvd.intro_left _ rfl
    obtain ⟨ℓ, hℓ, hℓs⟩ := Nat.exists_prime_and_dvd (n := x ^ 2 + x + 1) (by omega)
    exact false_of_prime_dvd hx2 hxe hx3 hℓ hℓs (hℓs.trans (hs3.trans hdvd))
  ·
    have hcop12 : Nat.Coprime r 12 := by
      rw [hr.coprime_iff_not_dvd]
      intro h
      have h12 : (12 : ℕ) = 2 * (2 * 3) := by norm_num
      rw [h12] at h
      rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h1)
      · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
        · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
        · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h2)
    have hg12 : Nat.gcd r 12 = 1 := hcop12
    have hgcd : Nat.gcd (x ^ r - 1) (x ^ 12 - 1) = x - 1 := by
      rw [Nat.pow_sub_one_gcd_pow_sub_one, hg12, pow_one]
    have hpow1 : 1 ≤ x ^ r := Nat.one_le_pow _ _ (by omega)
    have hNx : Nat.Coprime (x ^ r - 1) x := by
      have hN1 : x ^ r - 1 + 1 = x ^ r := by omega
      have hd1 : Nat.gcd (x ^ r - 1) x ∣ x ^ r - 1 := Nat.gcd_dvd_left _ _
      have hd2 : Nat.gcd (x ^ r - 1) x ∣ x ^ r - 1 + 1 := by
        rw [hN1]
        exact (Nat.gcd_dvd_right _ _).pow hr.ne_zero
      exact Nat.dvd_one.1 ((Nat.dvd_add_right hd1).1 hd2)
    have hcopA : Nat.Coprime (x ^ r - 1) (x ^ 12) := Nat.Coprime.pow_right 12 hNx
    have hF : orderF x = x ^ 12 * ((x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 *
        (x ^ 2 - x + 1) * (x ^ 4 - x ^ 2 + 1)) := by
      unfold orderF
      ring
    rw [hF] at hdvd
    have hNC : x ^ r - 1 ∣ (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 *
        (x ^ 2 - x + 1) * (x ^ 4 - x ^ 2 + 1) := hcopA.dvd_of_dvd_mul_left hdvd
    have hx1 : 1 ≤ x := by omega
    have hxx : x ≤ x ^ 2 := by nlinarith
    have hx24 : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hx12 : 1 ≤ x ^ 12 := Nat.one_le_pow _ _ (by omega)
    have hCA : (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 * (x ^ 2 - x + 1) *
        (x ^ 4 - x ^ 2 + 1) ∣ (x ^ 12 - 1) ^ 2 := by
      refine ⟨(x ^ 2 + x + 1) ^ 2 * (x ^ 2 - x + 1) * (x ^ 4 - x ^ 2 + 1), ?_⟩
      zify [hx1, hxx, hx24, hx12]
      ring
    have hNA : x ^ r - 1 ∣ (x ^ 12 - 1) ^ 2 := hNC.trans hCA
    have hg0 : 0 < x - 1 := by omega
    have hgN : x - 1 ∣ x ^ r - 1 := by
      rw [← hgcd]
      exact Nat.gcd_dvd_left _ _
    have hgA : x - 1 ∣ x ^ 12 - 1 := by
      rw [← hgcd]
      exact Nat.gcd_dvd_right _ _
    obtain ⟨N', hN'⟩ := hgN
    obtain ⟨A', hA'⟩ := hgA
    have hcopN' : Nat.Coprime N' A' := by
      have h1 : (x - 1) * Nat.gcd N' A' = (x - 1) * 1 := by
        rw [mul_one, ← Nat.gcd_mul_left, ← hN', ← hA', hgcd]
      exact Nat.eq_of_mul_eq_mul_left hg0 h1
    have hN'dvd : N' ∣ (x - 1) * A' ^ 2 := by
      have hA2 : (x - 1) * ((x - 1) * A' ^ 2) = (x ^ 12 - 1) ^ 2 := by
        rw [hA']
        ring
      have h1 : (x - 1) * N' ∣ (x - 1) * ((x - 1) * A' ^ 2) := by
        rw [hA2, ← hN']
        exact hNA
      exact Nat.dvd_of_mul_dvd_mul_left hg0 h1
    have hN'g : N' ∣ x - 1 := (Nat.Coprime.pow_right 2 hcopN').dvd_of_dvd_mul_right hN'dvd
    have hN'le : N' ≤ x - 1 := Nat.le_of_dvd hg0 hN'g
    have hNle : x ^ r - 1 ≤ (x - 1) * (x - 1) := by
      rw [hN']
      exact Nat.mul_le_mul le_rfl hN'le
    have hxr : x ^ 2 ≤ x ^ r := Nat.pow_le_pow_right (by omega) hr.two_le
    have hx2sq : x ^ 2 = (x - 1) * (x - 1) + 2 * (x - 1) + 1 := by
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

theorem not_dvd_orderF_pow_sub_one {b r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hdvd : (2 ^ (2 * b + 1)) ^ r - 1 ∣ orderF (2 ^ (2 * b + 1))) : False := by
  have hx2 : 2 ≤ 2 ^ (2 * b + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxe : 2 ∣ 2 ^ (2 * b + 1) := by
    rw [pow_succ]
    exact Dvd.intro_left _ rfl
  have hx3 : 2 ^ (2 * b + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact not_dvd_orderF_aux hx2 hxe hx3 hr hr2 hdvd

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big
