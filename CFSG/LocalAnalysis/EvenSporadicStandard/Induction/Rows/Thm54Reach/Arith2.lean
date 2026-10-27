module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm54Reach.Arith

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

private theorem one_le_two_pow_sub_one' {k : ℕ} (hk : 1 ≤ k) : 1 ≤ 2 ^ k - 1 := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem one_le_two_pow_add_one' (k : ℕ) : 1 ≤ 2 ^ k + 1 :=
  Nat.le_add_left 1 (2 ^ k)

private theorem one_le_mul'' {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  exact Nat.succ_le_of_lt
    (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one ha) (lt_of_lt_of_le Nat.zero_lt_one hb))

@[expose] def Thm54OrderLie (c : ℕ) : Prop :=
  (∃ m : ℕ, 3 ≤ m ∧ c = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) ∨
  (∃ m : ℕ, 3 ≤ m ∧
    c = 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1)))) ∨
  (∃ m : ℕ, 3 ≤ m ∧
    c = 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1)))) ∨
  (∃ m d : ℕ, 3 ≤ m ∧ (d = 1 ∨ d = 5) ∧
    c * d = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
      ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))) ∨
  (∃ m d : ℕ, 3 ≤ m ∧ (d = 1 ∨ d = 5) ∧
    c * d = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
      ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))))

theorem thm54Order_iff {c : ℕ} :
    Thm54Order c ↔
      (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ c = 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1))) ∨
        Thm54OrderLie c :=
  Iff.rfl

theorem Thm54OrderLie.gt {c : ℕ} (h : Thm54OrderLie c) : 95040 < c := by
  rcases h with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, d, hm, hd, hcd⟩ |
    ⟨m, d, hm, hd, hcd⟩
  · have h1 : 4096 ≤ 2 ^ (4 * m) := by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 63 ≤ 2 ^ (2 * m) - 1 := by
      have : 64 ≤ 2 ^ (2 * m) := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3 : 1 ≤ 2 ^ (4 * m) - 1 := one_le_two_pow_sub_one' (by omega)
    calc 95040 < 4096 * (63 * 1) := by norm_num
      _ ≤ 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  · have h1 : 95040 < 2 ^ (6 * m) := by
      calc 95040 < 2 ^ 17 := by norm_num
        _ ≤ 2 ^ (6 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (2 * m) - 1 := one_le_two_pow_sub_one' (by omega)
    have h3 : 1 ≤ 2 ^ (3 * m) + 1 := one_le_two_pow_add_one' _
    have h4 : 1 ≤ 2 ^ (4 * m) - 1 := one_le_two_pow_sub_one' (by omega)
    have hR : 1 ≤ (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1)) :=
      one_le_mul'' h2 (one_le_mul'' h3 h4)
    calc 95040 < 2 ^ (6 * m) := h1
      _ = 2 ^ (6 * m) * 1 := by ring
      _ ≤ 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))) :=
        Nat.mul_le_mul_left _ hR
  · have h1 : 95040 < 2 ^ (6 * m) := by
      calc 95040 < 2 ^ 17 := by norm_num
        _ ≤ 2 ^ (6 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (2 * m) - 1 := one_le_two_pow_sub_one' (by omega)
    have h3 : 1 ≤ 2 ^ (3 * m) - 1 := one_le_two_pow_sub_one' (by omega)
    have h4 : 1 ≤ 2 ^ (4 * m) - 1 := one_le_two_pow_sub_one' (by omega)
    have hR : 1 ≤ (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1)) :=
      one_le_mul'' h2 (one_le_mul'' h3 h4)
    calc 95040 < 2 ^ (6 * m) := h1
      _ = 2 ^ (6 * m) * 1 := by ring
      _ ≤ 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))) :=
        Nat.mul_le_mul_left _ hR
  · by_contra hle
    push Not at hle
    have hN : 2 ^ 30 ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by
      have hpow : 2 ^ 30 ≤ 2 ^ (10 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hR : 1 ≤ (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))) :=
        one_le_mul'' (one_le_two_pow_sub_one' (by omega))
          (one_le_mul'' (one_le_two_pow_add_one' _)
            (one_le_mul'' (one_le_two_pow_sub_one' (by omega))
              (one_le_two_pow_add_one' _)))
      calc 2 ^ 30 ≤ 2 ^ (10 * m) := hpow
        _ = 2 ^ (10 * m) * 1 := by ring
        _ ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := Nat.mul_le_mul_left _ hR
    have hd5 : d ≤ 5 := by rcases hd with rfl | rfl <;> norm_num
    have hlt : c * d < 2 ^ 30 := by
      calc c * d ≤ 95040 * 5 := Nat.mul_le_mul hle hd5
        _ < 2 ^ 30 := by norm_num
    rw [hcd] at hlt
    omega
  · by_contra hle
    push Not at hle
    have hN : 2 ^ 30 ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by
      have hpow : 2 ^ 30 ≤ 2 ^ (10 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hR : 1 ≤ (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))) :=
        one_le_mul'' (one_le_two_pow_sub_one' (by omega))
          (one_le_mul'' (one_le_two_pow_sub_one' (by omega))
            (one_le_mul'' (one_le_two_pow_sub_one' (by omega))
              (one_le_two_pow_sub_one' (by omega))))
      calc 2 ^ 30 ≤ 2 ^ (10 * m) := hpow
        _ = 2 ^ (10 * m) * 1 := by ring
        _ ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := Nat.mul_le_mul_left _ hR
    have hd5 : d ≤ 5 := by rcases hd with rfl | rfl <;> norm_num
    have hlt : c * d < 2 ^ 30 := by
      calc c * d ≤ 95040 * 5 := Nat.mul_le_mul hle hd5
        _ < 2 ^ 30 := by norm_num
    rw [hcd] at hlt
    omega

theorem Thm54Order.sz_eq_29120 {f : ℕ} (hf : 3 ≤ f)
    (h : 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1)) = 29120) : f = 3 := by
  by_contra hne
  have hf4 : 4 ≤ f := by omega
  have h1 : 256 ≤ 2 ^ (2 * f) := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 257 ≤ 2 ^ (2 * f) + 1 := by omega
  have h3 : 15 ≤ 2 ^ f - 1 := by
    have : 16 ≤ 2 ^ f := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
    omega
  have hge : 29120 < 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1)) := by
    calc 29120 < 256 * (257 * 15) := by norm_num
      _ ≤ 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [h] at hge
  omega

theorem Thm54Order.eq_29120_or_gt {c : ℕ} (hc : Thm54Order c) : c = 29120 ∨ 95040 < c := by
  rcases thm54Order_iff.1 hc with ⟨f, hf, _, rfl⟩ | hL
  · by_cases hf3 : f = 3
    · left
      rw [hf3]
      norm_num
    · right
      have hf4 : 4 ≤ f := by omega
      have h1 : 256 ≤ 2 ^ (2 * f) := by
        calc 256 = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 257 ≤ 2 ^ (2 * f) + 1 := by omega
      have h3 : 15 ≤ 2 ^ f - 1 := by
        have : 16 ≤ 2 ^ f := by
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf4
        omega
      calc 95040 < 256 * (257 * 15) := by norm_num
        _ ≤ 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1)) :=
          Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  · right
    exact Thm54OrderLie.gt hL

theorem Thm54Order.not_dvd_95040 {c : ℕ} (hc : Thm54Order c) : ¬ c ∣ 95040 := by
  rcases Thm54Order.eq_29120_or_gt hc with h | h
  · rw [h]
    decide
  · intro hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 95040) hdvd
    omega

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
