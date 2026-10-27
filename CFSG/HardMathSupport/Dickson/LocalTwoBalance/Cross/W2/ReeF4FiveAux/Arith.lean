module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux

@[expose] def orderF (x : ℕ) : ℕ :=
  x ^ 12 * (x - 1) ^ 2 * (x + 1) ^ 2 * (x ^ 2 + 1) ^ 2 * (x ^ 2 - x + 1) * (x ^ 4 - x ^ 2 + 1)

@[expose] def orderSz (Q : ℕ) : ℕ := Q ^ 2 * (Q - 1) * (Q ^ 2 + 1)

theorem odd_cofactor (b : ℕ) :
    Odd ((2 ^ (2 * b + 1) - 1) ^ 2 * (2 ^ (2 * b + 1) + 1) ^ 2 *
      ((2 ^ (2 * b + 1)) ^ 2 + 1) ^ 2 * ((2 ^ (2 * b + 1)) ^ 2 - 2 ^ (2 * b + 1) + 1) *
      ((2 ^ (2 * b + 1)) ^ 4 - (2 ^ (2 * b + 1)) ^ 2 + 1)) := by
  have hQe : Even (2 ^ (2 * b + 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hQ2 : 2 ≤ 2 ^ (2 * b + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * b + 1) = Q at hQe hQ2 ⊢
  have hQ2e : Even (Q ^ 2) := Nat.even_pow.2 ⟨hQe, by norm_num⟩
  have hQ4e : Even (Q ^ 4) := Nat.even_pow.2 ⟨hQe, by norm_num⟩
  have h1 : Q ≤ Q ^ 2 := by nlinarith
  have h2 : Q ^ 2 ≤ Q ^ 4 := by nlinarith
  refine Odd.mul (Odd.mul (Odd.mul (Odd.mul ?_ ?_) ?_) ?_) ?_
  · exact Odd.pow (Nat.Even.sub_odd (by omega) hQe odd_one)
  · exact Odd.pow hQe.add_one
  · exact Odd.pow hQ2e.add_one
  · exact ((Nat.even_sub h1).2 (iff_of_true hQ2e hQe)).add_one
  · exact ((Nat.even_sub h2).2 (iff_of_true hQ4e hQ2e)).add_one

theorem le_of_two_pow_dvd_orderF {b n : ℕ} (h : 2 ^ n ∣ orderF (2 ^ (2 * b + 1))) :
    n ≤ 12 * (2 * b + 1) := by
  unfold orderF at h
  simp only [mul_assoc] at h
  have hcop : Nat.Coprime (2 ^ n) ((2 ^ (2 * b + 1) - 1) ^ 2 * ((2 ^ (2 * b + 1) + 1) ^ 2 *
      (((2 ^ (2 * b + 1)) ^ 2 + 1) ^ 2 * (((2 ^ (2 * b + 1)) ^ 2 - 2 ^ (2 * b + 1) + 1) *
        ((2 ^ (2 * b + 1)) ^ 4 - (2 ^ (2 * b + 1)) ^ 2 + 1))))) := by
    refine Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ?_)
    simpa only [mul_assoc] using odd_cofactor b
  have h2 : 2 ^ n ∣ ((2 ^ (2 * b + 1)) ^ 12) := hcop.dvd_of_dvd_mul_right h
  rw [← pow_mul] at h2
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2 |>.trans (by omega)

theorem false_of_large {b r : ℕ} (hr7 : 7 ≤ r)
    (hdvd : orderSz ((2 ^ (2 * b + 1)) ^ r) ∣ orderF (2 ^ (2 * b + 1))) : False := by
  have hQ : (2 ^ (2 * b + 1)) ^ r = 2 ^ ((2 * b + 1) * r) := (pow_mul 2 (2 * b + 1) r).symm
  have hQ2 : (2 ^ ((2 * b + 1) * r)) ^ 2 = 2 ^ (2 * ((2 * b + 1) * r)) := by
    rw [← pow_mul, mul_comm]
  have h2 : 2 ^ (2 * ((2 * b + 1) * r)) ∣ orderSz ((2 ^ (2 * b + 1)) ^ r) := by
    unfold orderSz
    rw [hQ, hQ2]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
  have := le_of_two_pow_dvd_orderF (h2.trans hdvd)
  nlinarith

theorem false_of_prime_dvd {x ℓ : ℕ} (hx2 : 2 ≤ x) (hxe : 2 ∣ x) (hx3 : x % 3 = 2)
    (hℓ : ℓ.Prime) (hs : ℓ ∣ x ^ 2 + x + 1) (hF : ℓ ∣ orderF x) : False := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hxe
    have : 2 ∣ x ^ 2 + x + 1 := hs
    rw [hc] at this
    have h3 : 2 ∣ (2 * c) ^ 2 + 2 * c := ⟨2 * c ^ 2 + c, by ring⟩
    have := (Nat.dvd_add_right h3).1 (by simpa [add_assoc] using this)
    omega
  have hxℓ : ¬ ℓ ∣ x := by
    intro h
    have h1 : ℓ ∣ x * (x + 1) := Dvd.dvd.mul_right h _
    have : x ^ 2 + x + 1 = x * (x + 1) + 1 := by ring
    rw [this] at hs
    have := (Nat.dvd_add_right h1).1 hs
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hx24 : x ^ 2 ≤ x ^ 4 := by nlinarith
  unfold orderF at hF
  rcases (Nat.Prime.dvd_mul hℓ).1 hF with hF | hF
  · rcases (Nat.Prime.dvd_mul hℓ).1 hF with hF | hF
    · rcases (Nat.Prime.dvd_mul hℓ).1 hF with hF | hF
      · rcases (Nat.Prime.dvd_mul hℓ).1 hF with hF | hF
        · rcases (Nat.Prime.dvd_mul hℓ).1 hF with hF | hF
          · exact hxℓ (hℓ.dvd_of_dvd_pow hF)
          ·
            have hF := hℓ.dvd_of_dvd_pow hF
            have h3 : x ^ 2 + x + 1 = (x - 1) * (x + 2) + 3 := by
              obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
              simp only [Nat.add_sub_cancel]
              ring
            rw [h3] at hs
            have h4 := (Nat.dvd_add_right (Dvd.dvd.mul_right hF _)).1 hs
            have h5 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h4
            subst h5
            omega
        ·
          have hF := hℓ.dvd_of_dvd_pow hF
          have h3 : x ^ 2 + x + 1 = (x + 1) * x + 1 := by ring
          rw [h3] at hs
          have h4 := (Nat.dvd_add_right (Dvd.dvd.mul_right hF _)).1 hs
          exact hℓ.one_lt.ne' (Nat.dvd_one.1 h4)
      ·
        have hF := hℓ.dvd_of_dvd_pow hF
        have h3 : x ^ 2 + x + 1 = (x ^ 2 + 1) + x := by ring
        rw [h3] at hs
        exact hxℓ ((Nat.dvd_add_right hF).1 hs)
    ·
      have h3 : x ^ 2 + x + 1 = (x ^ 2 - x + 1) + 2 * x := by omega
      rw [h3] at hs
      have h4 := (Nat.dvd_add_right hF).1 hs
      rcases (Nat.Prime.dvd_mul hℓ).1 h4 with h5 | h5
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h5)
      · exact hxℓ h5
  ·
    have h3 : (x ^ 2 + x + 1) * (x ^ 2 - x + 1) = (x ^ 4 - x ^ 2 + 1) + 2 * x ^ 2 := by
      obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      subst hy
      zify [hxx, hx24]
      ring
    have h4 : ℓ ∣ (x ^ 4 - x ^ 2 + 1) + 2 * x ^ 2 := by
      rw [← h3]
      exact Dvd.dvd.mul_right hs _
    have h5 := (Nat.dvd_add_right hF).1 h4
    rcases (Nat.Prime.dvd_mul hℓ).1 h5 with h6 | h6
    · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h6)
    · exact hxℓ (hℓ.dvd_of_dvd_pow h6)

theorem false_of_three_aux {x : ℕ} (hx2 : 2 ≤ x) (hxe : 2 ∣ x) (hx3 : x % 3 = 2)
    (hdvd : orderSz (x ^ 3) ∣ orderF x) : False := by
  have hs3 : (x ^ 2 + x + 1) ∣ x ^ 3 - 1 := by
    have : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by
      obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      subst hy
      simp only [Nat.add_sub_cancel]
      zify [Nat.one_le_pow 3 (y + 1) (by omega)]
      ring
    rw [this]
    exact Dvd.intro_left _ rfl
  have hs : (x ^ 2 + x + 1) ∣ orderSz (x ^ 3) := by
    unfold orderSz
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hs3 _) _
  obtain ⟨ℓ, hℓ, hℓs⟩ := Nat.exists_prime_and_dvd (n := x ^ 2 + x + 1) (by nlinarith)
  exact false_of_prime_dvd hx2 hxe hx3 hℓ hℓs (hℓs.trans (hs.trans hdvd))

theorem false_of_three {b : ℕ}
    (hdvd : orderSz ((2 ^ (2 * b + 1)) ^ 3) ∣ orderF (2 ^ (2 * b + 1))) : False := by
  have hx2 : 2 ≤ 2 ^ (2 * b + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxe : 2 ∣ 2 ^ (2 * b + 1) := by
    rw [pow_succ]
    exact Dvd.intro_left _ rfl
  have hx3 : 2 ^ (2 * b + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact false_of_three_aux hx2 hxe hx3 hdvd

theorem false_of_orders {b r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : r ≠ 5)
    (hdvd : orderSz ((2 ^ (2 * b + 1)) ^ r) ∣ orderF (2 ^ (2 * b + 1))) : False := by
  by_cases h7 : 7 ≤ r
  · exact false_of_large h7 hdvd
  · have hr3 : r = 3 := by
      have : r < 7 := by omega
      interval_cases r <;> first | rfl | omega | (exfalso; revert hr; norm_num)
    subst hr3
    exact false_of_three hdvd

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4FiveAux
