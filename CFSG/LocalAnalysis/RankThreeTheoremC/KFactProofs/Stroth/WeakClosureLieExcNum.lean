module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

theorem dvd_sub_one_of_orderOf_eq_one' {p q : ℕ} (hq : 1 ≤ q)
    (h : orderOf ((q : ℕ) : ZMod p) = 1) : p ∣ q - 1 := by
  rw [orderOf_eq_one_iff] at h
  have : ((q - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hq, Nat.cast_one, h, sub_self]
  exact (ZMod.natCast_eq_zero_iff (q - 1) p).1 this

theorem orderOf_eq_one_of_dvd_sub_one' {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q - 1) :
    orderOf ((q : ℕ) : ZMod p) = 1 := by
  rw [orderOf_eq_one_iff]
  have := (ZMod.natCast_eq_zero_iff (q - 1) p).2 h
  rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at this
  exact this

theorem dvd_add_one_of_orderOf_eq_two' {p q : ℕ} (hp : p.Prime)
    (he : orderOf ((q : ℕ) : ZMod p) = 2) : p ∣ q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p)
  have h2 : x ^ 2 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have h1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at he; omega
  have : (x - 1) * (x + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · exact (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h)

theorem orderOf_eq_two_of_dvd_add_one' {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ q + 1) : orderOf ((q : ℕ) : ZMod p) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  have hq : (q : ZMod p) = -1 := by
    rw [Nat.cast_add, Nat.cast_one] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hne : (-1 : ZMod p) ≠ 1 := by
    intro h1
    have : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
      ((ZMod.natCast_eq_zero_iff 2 p).1 this))
  rw [hq]
  exact orderOf_eq_prime (by norm_num) hne

theorem dvd_phi3_of_orderOf' {p q : ℕ} (hp : p.Prime) (he : orderOf ((q : ℕ) : ZMod p) = 3) :
    p ∣ q ^ 2 + q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p)
  have h3 : x ^ 3 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have h1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at he; omega
  have : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · exact (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h)

theorem dvd_phi4_of_orderOf' {p q : ℕ} (hp : p.Prime) (he : orderOf ((q : ℕ) : ZMod p) = 4) :
    p ∣ q ^ 2 + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p)
  have h4 : x ^ 4 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have h1 : x ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    omega
  have : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · exact (ZMod.natCast_eq_zero_iff _ _).1 (by push_cast; exact h)

theorem dvd_phi6_of_orderOf' {p q : ℕ} (hp : p.Prime) (he : orderOf ((q : ℕ) : ZMod p) = 6) :
    p ∣ q ^ 2 - q + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  set x : ZMod p := (q : ZMod p)
  have h6 : x ^ 6 = 1 := by rw [← he]; exact pow_orderOf_eq_one x
  have h3 : x ^ 3 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    omega
  have h2 : x + 1 ≠ 0 := fun h => by
    have : x ^ 2 = 1 := by linear_combination (x - 1) * h
    have := orderOf_dvd_of_pow_eq_one this
    rw [he] at this
    omega
  have hq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hq3 : (x ^ 3 - 1) * (x ^ 3 + 1) = 0 := by linear_combination h6
  have h3' : x ^ 3 + 1 = 0 := by
    rcases mul_eq_zero.1 hq3 with h | h
    · exact absurd (sub_eq_zero.1 h) h3
    · exact h
  have : (x + 1) * (x ^ 2 - x + 1) = 0 := by linear_combination h3'
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h h2
  · refine (ZMod.natCast_eq_zero_iff _ _).1 ?_
    rw [Nat.cast_add, Nat.cast_sub hq]
    push_cast
    exact h

theorem orderOf_natCast_pos' {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    0 < orderOf (q : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  refine Nat.pos_of_ne_zero fun h => ?_
  have h' := h ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have := hp.one_lt
  rw [zero_dvd_iff] at h'
  omega

theorem exists_inv_arith {p q e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (he : orderOf ((q : ℕ) : ZMod p) = e) (s : ℤ) (k : ℕ)
    (hs : (s = 1 ∧ ¬ e ∣ k) ∨ (s = -1 ∧ e ∣ k)) :
    ∃ q' : ℕ, q * q' ≡ 1 [MOD p] ∧ ¬ (p : ℤ) ∣ (q' : ℤ) ^ k * s - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have he0 : 0 < e := he ▸ orderOf_natCast_pos' hp hpq
  have hqe : (q : ZMod p) ^ e = 1 := by rw [← he]; exact pow_orderOf_eq_one _
  refine ⟨q ^ (e - 1), ?_, ?_⟩
  · refine (ZMod.natCast_eq_natCast_iff _ _ _).1 ?_
    rw [Nat.cast_mul, Nat.cast_pow, ← pow_succ', Nat.sub_add_cancel he0, hqe, Nat.cast_one]
  · intro hdvd
    have h0 : (((q ^ (e - 1) : ℕ) : ℤ) ^ k * s - 1 : ℤ) = ((q : ℤ) ^ ((e - 1) * k)) * s - 1 := by
      push_cast
      rw [← pow_mul]
    rw [h0] at hdvd
    have h1 : ((q : ZMod p) ^ ((e - 1) * k)) * (s : ZMod p) = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
      push_cast at this
      linear_combination this
    rcases hs with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
    · rw [Int.cast_one, mul_one] at h1
      have h2 : e ∣ (e - 1) * k := by
        have := orderOf_dvd_of_pow_eq_one h1
        rwa [he] at this
      apply hk
      have h3 : e ∣ e * k - (e - 1) * k := Nat.dvd_sub (dvd_mul_right e k) h2
      have h4 : e * k - (e - 1) * k = k := by
        obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [add_mul, one_mul]
        omega
      rwa [h4] at h3
    · obtain ⟨m, rfl⟩ := hk
      have h5 : (q : ZMod p) ^ ((e - 1) * (e * m)) = 1 := by
        rw [show (e - 1) * (e * m) = e * ((e - 1) * m) by ring, pow_mul, hqe, one_pow]
      rw [h5, Int.cast_neg, Int.cast_one, one_mul] at h1
      have h6 : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination -h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        ((ZMod.natCast_eq_zero_iff 2 p).1 h6))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
