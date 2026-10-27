module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpArith

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

theorem one_le_orderOf_two_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    1 ≤ orderOf (2 : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hd : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2
  exact Nat.pos_of_dvd_of_pos hd (by omega)

theorem pow_le_pow_succ_div_sub_one {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (n : ℕ) :
    q ^ n ≤ q ^ (n + 1) / (p - 1) := by
  rw [Nat.le_div_iff_mul_le (by omega : 0 < p - 1)]
  calc q ^ n * (p - 1) ≤ q ^ n * q := Nat.mul_le_mul_left _ (by omega)
    _ = q ^ (n + 1) := (pow_succ q n).symm

theorem triality_growth_lt {q e : ℕ} (he : e < q) (hq : 5 ≤ q) :
    1024 * e * q ^ 28 < 2 ^ (q ^ 3) := by
  have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
  have h1 : 1024 * e * q ^ 28 ≤ 1024 * q ^ 29 := by
    have h := Nat.mul_le_mul_right (q ^ 28) he.le
    have hq29 : q ^ 29 = q * q ^ 28 := by ring
    calc 1024 * e * q ^ 28 = 1024 * (e * q ^ 28) := by ring
      _ ≤ 1024 * (q * q ^ 28) := Nat.mul_le_mul_left 1024 h
      _ = 1024 * q ^ 29 := by rw [hq29]
  rcases (show q = 5 ∨ 6 ≤ q by omega) with rfl | h6
  · exact lt_of_le_of_lt h1 (by norm_num)
  · have h2 : q ^ 29 < 2 ^ (29 * q) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_lt_pow_left hq2 (by norm_num)
    have h4 : 6 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h6 2
    have h4' : 6 ^ 2 * q ≤ q ^ 2 * q := Nat.mul_le_mul_right q h4
    have h5 : 10 + 29 * q ≤ q ^ 3 := by
      have hq3 : q ^ 2 * q = q ^ 3 := by ring
      linarith
    calc 1024 * e * q ^ 28 ≤ 1024 * q ^ 29 := h1
      _ < 1024 * 2 ^ (29 * q) := by gcongr
      _ = 2 ^ (10 + 29 * q) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ (q ^ 3) := Nat.pow_le_pow_right (by norm_num) h5

theorem twistedE6_growth_lt {q e : ℕ} (he : e < q) (hq : 5 ≤ q) :
    1024 * e * q ^ 78 < 2 ^ (q ^ 5) := by
  have hq2 : q < 2 ^ q := Nat.lt_two_pow_self
  have h1 : 1024 * e * q ^ 78 ≤ 1024 * q ^ 79 := by
    have h := Nat.mul_le_mul_right (q ^ 78) he.le
    have hq79 : q ^ 79 = q * q ^ 78 := by ring
    calc 1024 * e * q ^ 78 = 1024 * (e * q ^ 78) := by ring
      _ ≤ 1024 * (q * q ^ 78) := Nat.mul_le_mul_left 1024 h
      _ = 1024 * q ^ 79 := by rw [hq79]
  have h2 : q ^ 79 < 2 ^ (79 * q) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left hq2 (by norm_num)
  have h4 : 5 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h4' : 5 ^ 4 * q ≤ q ^ 4 * q := Nat.mul_le_mul_right q h4
  have h5 : 10 + 79 * q ≤ q ^ 5 := by
    have hq5 : q ^ 4 * q = q ^ 5 := by ring
    linarith
  calc 1024 * e * q ^ 78 ≤ 1024 * q ^ 79 := h1
    _ < 1024 * 2 ^ (79 * q) := by gcongr
    _ = 2 ^ (10 + 79 * q) := by rw [pow_add]; norm_num
    _ ≤ 2 ^ (q ^ 5) := Nat.pow_le_pow_right (by norm_num) h5

theorem card_aut_triality_lt {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    1024 * e * (p ^ e) ^ 28 < 2 ^ (orderOf (2 : ZMod p) * ((p ^ e) ^ 4 / (p - 1))) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  by_cases hpe : p = 3 ∧ e = 1
  · obtain ⟨rfl, rfl⟩ := hpe
    rw [orderOf_two_zmod_three]
    norm_num
  · have hq5 : 5 ≤ p ^ e := by
      by_cases h3 : p = 3
      · have he2 : 2 ≤ e := by omega
        calc 5 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2
          _ = p ^ e := by rw [h3]
      · have hp4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        have hp5 : 5 ≤ p := by omega
        exact hp5.trans (Nat.le_self_pow (by omega) p)
    have hpq : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    have hee : e < p ^ e := Nat.lt_pow_self (by omega)
    have hM : (p ^ e) ^ 3 ≤ (p ^ e) ^ 4 / (p - 1) :=
      pow_le_pow_succ_div_sub_one (by omega) hpq 3
    have hd : 1 ≤ orderOf (2 : ZMod p) := one_le_orderOf_two_zmod hp2
    have hE : (p ^ e) ^ 3 ≤ orderOf (2 : ZMod p) * ((p ^ e) ^ 4 / (p - 1)) := by
      calc (p ^ e) ^ 3 ≤ (p ^ e) ^ 4 / (p - 1) := hM
        _ = 1 * ((p ^ e) ^ 4 / (p - 1)) := (one_mul _).symm
        _ ≤ orderOf (2 : ZMod p) * ((p ^ e) ^ 4 / (p - 1)) := Nat.mul_le_mul_right _ hd
    exact lt_of_lt_of_le (triality_growth_lt hee hq5) (Nat.pow_le_pow_right (by norm_num) hE)

theorem card_aut_twistedE6_lt {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) :
    1024 * e * (p ^ e) ^ 78 < 2 ^ (orderOf (2 : ZMod p) * ((p ^ e) ^ 6 / (p - 1))) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  by_cases hpe : p = 3 ∧ e = 1
  · obtain ⟨rfl, rfl⟩ := hpe
    rw [orderOf_two_zmod_three]
    calc 1024 * 1 * (3 ^ 1) ^ 78 < 2 ^ 136 := by norm_num
      _ ≤ 2 ^ (2 * ((3 ^ 1) ^ 6 / (3 - 1))) := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · have hq5 : 5 ≤ p ^ e := by
      by_cases h3 : p = 3
      · have he2 : 2 ≤ e := by omega
        calc 5 ≤ 3 ^ 2 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he2
          _ = p ^ e := by rw [h3]
      · have hp4 : p ≠ 4 := by
          rintro rfl
          norm_num at hp
        have hp5 : 5 ≤ p := by omega
        exact hp5.trans (Nat.le_self_pow (by omega) p)
    have hpq : p ≤ p ^ e := Nat.le_self_pow (by omega) p
    have hee : e < p ^ e := Nat.lt_pow_self (by omega)
    have hM : (p ^ e) ^ 5 ≤ (p ^ e) ^ 6 / (p - 1) :=
      pow_le_pow_succ_div_sub_one (by omega) hpq 5
    have hd : 1 ≤ orderOf (2 : ZMod p) := one_le_orderOf_two_zmod hp2
    have hE : (p ^ e) ^ 5 ≤ orderOf (2 : ZMod p) * ((p ^ e) ^ 6 / (p - 1)) := by
      calc (p ^ e) ^ 5 ≤ (p ^ e) ^ 6 / (p - 1) := hM
        _ = 1 * ((p ^ e) ^ 6 / (p - 1)) := (one_mul _).symm
        _ ≤ orderOf (2 : ZMod p) * ((p ^ e) ^ 6 / (p - 1)) := Nat.mul_le_mul_right _ hd
    exact lt_of_lt_of_le (twistedE6_growth_lt hee hq5) (Nat.pow_le_pow_right (by norm_num) hE)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

end
