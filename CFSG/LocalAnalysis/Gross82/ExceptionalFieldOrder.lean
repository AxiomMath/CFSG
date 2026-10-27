module
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.RankThree.PartTwo.Sec11.Item116R2ZNum
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.Gross82.ExceptionalFieldOrder

open CFSG.ComponentClassification.CatLeaf

private theorem minus_ne_zero {s d : ℕ} (hs : 2 ≤ s) (hd : d ≠ 0) : s ^ d - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))

private theorem minus_cube_mono {s d : ℕ} (hs : 2 ≤ s) (hd : d ≠ 0) :
    padicValNat 3 (s ^ d - 1) ≤ padicValNat 3 ((s ^ 3) ^ d - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : 2 ≤ s ^ 3 := by have := Nat.one_lt_pow (by decide : 3 ≠ 0) (by omega : 1 < s); omega
  have hdiv : s ^ d - 1 ∣ (s ^ 3) ^ d - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (s ^ d) 1 3
    simpa only [one_pow, ← pow_mul, Nat.mul_comm d 3] using h
  exact (padicValNat_dvd_iff_le (minus_ne_zero hs3 hd)).mp (pow_padicValNat_dvd.trans hdiv)

private theorem plus_cube_mono (s d : ℕ) :
    padicValNat 3 (s ^ d + 1) ≤ padicValNat 3 ((s ^ 3) ^ d + 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdiv : s ^ d + 1 ∣ (s ^ 3) ^ d + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (s ^ d) 1 (by decide : Odd 3)
    simpa only [one_pow, ← pow_mul, Nat.mul_comm d 3] using h
  exact (padicValNat_dvd_iff_le (Nat.succ_ne_zero _)).mp (pow_padicValNat_dvd.trans hdiv)

private theorem even_factor_cube {s k : ℕ} (hs : 2 ≤ s) (h3 : ¬ 3 ∣ s) (hk : k ≠ 0) :
    padicValNat 3 ((s ^ 3) ^ (2 * k) - 1) = padicValNat 3 (s ^ (2 * k) - 1) + 1 := by
  have hsk : 2 ≤ s ^ k := by have := Nat.one_lt_pow hk (by omega : 1 < s); omega
  have h3k : ¬ 3 ∣ s ^ k := fun h => h3 (Nat.prime_three.dvd_of_dvd_pow h)
  have h := CFSG.RankThree.PartTwo.Sec11.padicValNat_cube_sq_sub_one hsk h3k
  have heq : ((s ^ k) ^ 3) ^ 2 = (s ^ 3) ^ (2 * k) := by
    simp only [← pow_mul]
    congr 1
    omega
  have heq' : (s ^ k) ^ 2 = s ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k 2]
  simpa only [heq, heq'] using h

private theorem e6_numerator_val {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .E6 n s) =
      36 * padicValNat 3 s + padicValNat 3 (s ^ 12 - 1) +
      padicValNat 3 (s ^ 9 - 1) + padicValNat 3 (s ^ 8 - 1) +
      padicValNat 3 (s ^ 6 - 1) + padicValNat 3 (s ^ 5 - 1) +
      padicValNat 3 (s ^ 2 - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hminus : ∀ d, d ≠ 0 → s ^ d - 1 ≠ 0 := fun d hd => minus_ne_zero hs hd
  have hs0 : s ≠ 0 := by omega
  have hp36 : s ^ 36 ≠ 0 := pow_ne_zero _ hs0
  have h12 : s ^ 12 - 1 ≠ 0 := hminus 12 (by decide)
  have h9 : s ^ 9 - 1 ≠ 0 := hminus 9 (by decide)
  have h8 : s ^ 8 - 1 ≠ 0 := hminus 8 (by decide)
  have h6 : s ^ 6 - 1 ≠ 0 := hminus 6 (by decide)
  have h5 : s ^ 5 - 1 ≠ 0 := hminus 5 (by decide)
  have h2 : s ^ 2 - 1 ≠ 0 := hminus 2 (by decide)
  simp only [lieOrderNumerator]
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hp36 h12) h9) h8) h6) h5) h2,
    padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero hp36 h12) h9) h8) h6) h5,
    padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hp36 h12) h9) h8) h6,
    padicValNat.mul (mul_ne_zero (mul_ne_zero hp36 h12) h9) h8,
    padicValNat.mul (mul_ne_zero hp36 h12) h9,
    padicValNat.mul hp36 h12, padicValNat.pow]

private theorem twisted_e6_numerator_val {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .twistedE6 n s) =
      36 * padicValNat 3 s + padicValNat 3 (s ^ 12 - 1) +
      padicValNat 3 (s ^ 9 + 1) + padicValNat 3 (s ^ 8 - 1) +
      padicValNat 3 (s ^ 6 - 1) + padicValNat 3 (s ^ 5 + 1) +
      padicValNat 3 (s ^ 2 - 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hminus : ∀ d, d ≠ 0 → s ^ d - 1 ≠ 0 := fun d hd => minus_ne_zero hs hd
  have hs0 : s ≠ 0 := by omega
  have hp36 : s ^ 36 ≠ 0 := pow_ne_zero _ hs0
  have h12 : s ^ 12 - 1 ≠ 0 := hminus 12 (by decide)
  have h9 : s ^ 9 - 1 ≠ 0 := hminus 9 (by decide)
  have h8 : s ^ 8 - 1 ≠ 0 := hminus 8 (by decide)
  have h6 : s ^ 6 - 1 ≠ 0 := hminus 6 (by decide)
  have h5 : s ^ 5 - 1 ≠ 0 := hminus 5 (by decide)
  have h2 : s ^ 2 - 1 ≠ 0 := hminus 2 (by decide)
  simp only [lieOrderNumerator]
  have hp9 : s ^ 9 + 1 ≠ 0 := Nat.succ_ne_zero _
  have hp5 : s ^ 5 + 1 ≠ 0 := Nat.succ_ne_zero _
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hp36 h12) hp9) h8) h6) hp5) h2,
    padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero hp36 h12) hp9) h8) h6) hp5,
    padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hp36 h12) hp9) h8) h6,
    padicValNat.mul (mul_ne_zero (mul_ne_zero hp36 h12) hp9) h8,
    padicValNat.mul (mul_ne_zero hp36 h12) hp9,
    padicValNat.mul hp36 h12, padicValNat.pow]

private theorem gcd_three_val_le (x : ℕ) : padicValNat 3 (Nat.gcd 3 x) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (padicValNat_dvd_iff_le (p := 3) (by decide : (3 : ℕ) ≠ 0)).mp
    (pow_padicValNat_dvd.trans (Nat.gcd_dvd_left 3 x))
  simpa only [padicValNat_self] using h

private theorem characteristic_factors {s : ℕ} (hs : 2 ≤ s) (h3 : 3 ∣ s) {d : ℕ}
    (hd : d ≠ 0) : padicValNat 3 (s ^ d - 1) = 0 ∧ padicValNat 3 (s ^ d + 1) = 0 := by
  have hp : 3 ∣ s ^ d := h3.trans (dvd_pow_self s hd)
  have hpos : 1 ≤ s ^ d := Nat.one_le_pow _ _ (by omega)
  exact ⟨padicValNat.eq_zero_of_not_dvd (by omega), padicValNat.eq_zero_of_not_dvd (by omega)⟩

theorem padicValNat_three_lieOrder_e6_cube_lt {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .E6 n s) +
      padicValNat 3 (lieOrderDivisor .E6 n (s ^ 3)) <
    padicValNat 3 (lieOrderNumerator .E6 n (s ^ 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : 2 ≤ s ^ 3 := by have := Nat.one_lt_pow (by decide : 3 ≠ 0) (by omega : 1 < s); omega
  rw [e6_numerator_val hs, e6_numerator_val hs3, padicValNat.pow]
  by_cases h3 : 3 ∣ s
  · have h3cube : 3 ∣ s ^ 3 := h3.trans (dvd_pow_self s (by decide))
    have hsmall : ∀ {d : ℕ}, d ≠ 0 → padicValNat 3 (s ^ d - 1) = 0 ∧
        padicValNat 3 (s ^ d + 1) = 0 := fun hd => characteristic_factors hs h3 hd
    have hlarge : ∀ {d : ℕ}, d ≠ 0 → padicValNat 3 ((s ^ 3) ^ d - 1) = 0 ∧
        padicValNat 3 ((s ^ 3) ^ d + 1) = 0 := fun hd => characteristic_factors hs3 h3cube hd
    simp only [hsmall (by decide : 12 ≠ 0) |>.1, hsmall (by decide : 9 ≠ 0) |>.1,
      hsmall (by decide : 8 ≠ 0) |>.1, hsmall (by decide : 6 ≠ 0) |>.1,
      hsmall (by decide : 5 ≠ 0) |>.1, hsmall (by decide : 2 ≠ 0) |>.1,
      hlarge (by decide : 12 ≠ 0) |>.1, hlarge (by decide : 9 ≠ 0) |>.1,
      hlarge (by decide : 8 ≠ 0) |>.1, hlarge (by decide : 6 ≠ 0) |>.1,
      hlarge (by decide : 5 ≠ 0) |>.1, hlarge (by decide : 2 ≠ 0) |>.1, add_zero]
    have hd := gcd_three_val_le (s ^ 3 - 1)
    have hv := one_le_padicValNat_of_dvd (by omega : s ≠ 0) h3
    simpa only [lieOrderDivisor] using (by omega :
      36 * padicValNat 3 s + padicValNat 3 (Nat.gcd 3 (s ^ 3 - 1)) <
        36 * (3 * padicValNat 3 s))
  · have h12 := even_factor_cube (k := 6) hs h3 (by decide)
    have h8 := even_factor_cube (k := 4) hs h3 (by decide)
    have h6 := even_factor_cube (k := 3) hs h3 (by decide)
    have h2 := even_factor_cube (k := 1) hs h3 (by decide)
    have h9 := minus_cube_mono (d := 9) hs (by decide)
    have h5 := minus_cube_mono (d := 5) hs (by decide)
    have hd := gcd_three_val_le (s ^ 3 - 1)
    simp only [Nat.reduceMul] at h12 h8 h6 h2
    rw [lieOrderDivisor]
    omega

theorem padicValNat_three_lieOrder_twistedE6_cube_lt {s n : ℕ} (hs : 2 ≤ s) :
    padicValNat 3 (lieOrderNumerator .twistedE6 n s) +
      padicValNat 3 (lieOrderDivisor .twistedE6 n (s ^ 3)) <
    padicValNat 3 (lieOrderNumerator .twistedE6 n (s ^ 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs3 : 2 ≤ s ^ 3 := by have := Nat.one_lt_pow (by decide : 3 ≠ 0) (by omega : 1 < s); omega
  rw [twisted_e6_numerator_val hs, twisted_e6_numerator_val hs3, padicValNat.pow]
  by_cases h3 : 3 ∣ s
  · have h3cube : 3 ∣ s ^ 3 := h3.trans (dvd_pow_self s (by decide))
    have hsmall : ∀ {d : ℕ}, d ≠ 0 → padicValNat 3 (s ^ d - 1) = 0 ∧
        padicValNat 3 (s ^ d + 1) = 0 := fun hd => characteristic_factors hs h3 hd
    have hlarge : ∀ {d : ℕ}, d ≠ 0 → padicValNat 3 ((s ^ 3) ^ d - 1) = 0 ∧
        padicValNat 3 ((s ^ 3) ^ d + 1) = 0 := fun hd => characteristic_factors hs3 h3cube hd
    simp only [hsmall (by decide : 12 ≠ 0) |>.1, hsmall (by decide : 9 ≠ 0) |>.2,
      hsmall (by decide : 8 ≠ 0) |>.1, hsmall (by decide : 6 ≠ 0) |>.1,
      hsmall (by decide : 5 ≠ 0) |>.2, hsmall (by decide : 2 ≠ 0) |>.1,
      hlarge (by decide : 12 ≠ 0) |>.1, hlarge (by decide : 9 ≠ 0) |>.2,
      hlarge (by decide : 8 ≠ 0) |>.1, hlarge (by decide : 6 ≠ 0) |>.1,
      hlarge (by decide : 5 ≠ 0) |>.2, hlarge (by decide : 2 ≠ 0) |>.1, add_zero]
    have hd := gcd_three_val_le (s ^ 3 + 1)
    have hv := one_le_padicValNat_of_dvd (by omega : s ≠ 0) h3
    simpa only [lieOrderDivisor] using (by omega :
      36 * padicValNat 3 s + padicValNat 3 (Nat.gcd 3 (s ^ 3 + 1)) <
        36 * (3 * padicValNat 3 s))
  · have h12 := even_factor_cube (k := 6) hs h3 (by decide)
    have h8 := even_factor_cube (k := 4) hs h3 (by decide)
    have h6 := even_factor_cube (k := 3) hs h3 (by decide)
    have h2 := even_factor_cube (k := 1) hs h3 (by decide)
    have h9 := plus_cube_mono s 9
    have h5 := plus_cube_mono s 5
    have hd := gcd_three_val_le (s ^ 3 + 1)
    simp only [Nat.reduceMul] at h12 h8 h6 h2
    rw [lieOrderDivisor]
    omega

end CFSG.LocalAnalysis.Gross82.ExceptionalFieldOrder
