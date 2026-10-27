module

public import CFSG.CharacterTheory.Wreathed.Coordinates

public section

namespace CFSG.Wreathed

theorem two_factorization_eq_one_of_mod_four (a : ℕ) (ha : a % 4 = 2) :
    a.factorization 2 = 1 := by
  have ha0 : a ≠ 0 := by omega
  have h2 : 2 ^ 1 ∣ a := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  have h4 : ¬2 ^ 2 ∣ a := by
    intro h
    have hzero := Nat.dvd_iff_mod_eq_zero.mp h
    norm_num at hzero
    omega
  have hlo := (Nat.prime_two.pow_dvd_iff_le_factorization ha0).mp h2
  have hhi : ¬2 ≤ a.factorization 2 := by
    intro h
    exact h4 ((Nat.prime_two.pow_dvd_iff_le_factorization ha0).mpr h)
  omega

theorem mod_twice_power_of_two_factorization (a n : ℕ) (ha : a ≠ 0)
    (hf : a.factorization 2 = n) : a % (2 * 2 ^ n) = 2 ^ n := by
  have hdiv : 2 ^ n ∣ a :=
    (Nat.prime_two.pow_dvd_iff_le_factorization ha).mpr (by omega)
  have hnot : ¬(2 * 2 ^ n) ∣ a := by
    intro h
    have h' : 2 ^ (n + 1) ∣ a := by simpa only [pow_succ, Nat.mul_comm] using h
    have hle := (Nat.prime_two.pow_dvd_iff_le_factorization ha).mp h'
    omega
  obtain ⟨b, hb⟩ := hdiv
  have hodd : b % 2 = 1 := by
    have hrem := Nat.mod_lt b (by decide : 0 < (2 : ℕ))
    by_contra hne
    have heven : 2 ∣ b := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    obtain ⟨c, hc⟩ := heven
    apply hnot
    refine ⟨c, ?_⟩
    rw [hb, hc]
    ring
  have hdecomp := Nat.mod_add_div b 2
  rw [hodd] at hdecomp
  rw [hb, ← hdecomp]
  rw [mul_add]
  rw [show 2 ^ n * (2 * (b / 2)) = b / 2 * (2 * 2 ^ n) by ring]
  rw [Nat.add_mul_mod_self_right, mul_one]
  exact Nat.mod_eq_of_lt (by have hp := pow_pos (by decide : 0 < (2 : ℕ)) n; omega)

theorem two_part_square_sub_one_split (q n : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 1)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q - 1).factorization 2 = n := by
  have hqm : q - 1 ≠ 0 := by omega
  have hqp : q + 1 ≠ 0 := by omega
  have hlow := two_factorization_eq_one_of_mod_four (q + 1) (by omega)
  have hfac : (q ^ 2 - 1).factorization 2 = (q - 1).factorization 2 + 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1,
      Nat.factorization_mul hqp hqm]
    simp only [Finsupp.add_apply, hlow]
    omega
  have hexp : (q ^ 2 - 1).factorization 2 = n + 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    simpa only [pow_succ, Nat.mul_comm] using hpart
  omega

theorem two_part_square_sub_one_nonsplit (q n : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 3)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q + 1).factorization 2 = n := by
  have hqm : q - 1 ≠ 0 := by omega
  have hqp : q + 1 ≠ 0 := by omega
  have hlow := two_factorization_eq_one_of_mod_four (q - 1) (by omega)
  have hfac : (q ^ 2 - 1).factorization 2 = (q + 1).factorization 2 + 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1,
      Nat.factorization_mul hqp hqm]
    simp only [Finsupp.add_apply, hlow]
  have hexp : (q ^ 2 - 1).factorization 2 = n + 1 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ))
    simpa only [pow_succ, Nat.mul_comm] using hpart
  omega

theorem parameter_mod_twice_modulus_split (q n : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 1)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q : ℤ) ≡ 1 + (2 ^ n : ℕ) [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  have hf := two_part_square_sub_one_split q n hq hq4 hpart
  have hm := mod_twice_power_of_two_factorization (q - 1) n (by omega) hf
  have hmod : ((q - 1 : ℕ) : ℤ) ≡ (2 ^ n : ℕ) [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
    rw [Int.natCast_modEq_iff]
    change (q - 1) % (2 * 2 ^ n) = 2 ^ n % (2 * 2 ^ n)
    rw [hm, Nat.mod_eq_of_lt (by have hp := pow_pos (by decide : 0 < (2 : ℕ)) n; omega)]
  have hadd := hmod.add_left 1
  rw [Int.natCast_sub (by omega : 1 ≤ q), Nat.cast_one,
    show 1 + ((q : ℤ) - 1) = q by ring] at hadd
  exact hadd

theorem parameter_mod_twice_modulus_nonsplit (q n : ℕ) (hq : 3 ≤ q)
    (hq4 : q % 4 = 3)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    (q : ℤ) ≡ -1 + (2 ^ n : ℕ) [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
  have hf := two_part_square_sub_one_nonsplit q n hq hq4 hpart
  have hm := mod_twice_power_of_two_factorization (q + 1) n (by omega) hf
  have hmod : ((q + 1 : ℕ) : ℤ) ≡ (2 ^ n : ℕ) [ZMOD ((2 * 2 ^ n : ℕ) : ℤ)] := by
    rw [Int.natCast_modEq_iff]
    change (q + 1) % (2 * 2 ^ n) = 2 ^ n % (2 * 2 ^ n)
    rw [hm, Nat.mod_eq_of_lt (by have hp := pow_pos (by decide : 0 < (2 : ℕ)) n; omega)]
  have hadd := hmod.add_left (-1)
  rw [Nat.cast_add, Nat.cast_one,
    show -1 + ((q : ℤ) + 1) = q by ring] at hadd
  exact hadd

end CFSG.Wreathed
