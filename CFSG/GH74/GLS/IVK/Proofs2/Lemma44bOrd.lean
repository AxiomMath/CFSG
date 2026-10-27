module

public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma44bOrd

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem card_statedProj_statedSL_three_mul {F : Type} [Field F] [Finite F] :
    Nat.card (StatedProj (StatedSL 3 F)) * Nat.gcd 3 (Nat.card F - 1) =
      Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F)
    (by norm_num : 1 ≤ 3)
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)] at h
  have h1 : Nat.gcd 3 (Nat.card F - 1) ∣ Nat.card F - 1 := Nat.gcd_dvd_right _ _
  have h2 : Nat.card F - 1 ∣ Nat.card F ^ 3 - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 3
  have hd : Nat.gcd 3 (Nat.card F - 1) ∣
      Nat.card F ^ (3 * (3 - 1) / 2) * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (h1.trans h2) _) _
  rw [h, Nat.div_mul_cancel hd, show 3 * (3 - 1) / 2 = 3 by norm_num, mul_assoc]

theorem card_statedProj_statedSU_three_mul {p n : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p n F) :
    Nat.card (StatedProj (StatedSU 3 (p ^ n) F)) * Nat.gcd 3 (p ^ n + 1) =
      (p ^ n) ^ 3 * ((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 + 1) := by
  have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := F) h.prime h.one_le
    (by rw [h.card, ← pow_mul, mul_comm]) (by norm_num : 2 ≤ 3)
  have hq : 1 ≤ p ^ n := Nat.one_le_pow _ _ h.prime.pos
  have e2 : (((p ^ n : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (p ^ n) ^ 2 - 1 := by
    have : (((p ^ n : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((p ^ n) ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
      push_cast
      first | done | ring
    rw [this, Int.toNat_natCast]
  have e3 : (((p ^ n : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (p ^ n) ^ 3 + 1 := by
    have : (((p ^ n : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((p ^ n) ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      first | done | ring
    rw [this, Int.toNat_natCast]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ n : ℕ) : ℤ) ^ i - (-1) ^ i).toNat =
      ((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num), e2, e3]
  rw [hprod, show 3 * (3 - 1) / 2 = 3 by norm_num] at h1
  have h2 : Nat.gcd 3 (p ^ n + 1) ∣ p ^ n + 1 := Nat.gcd_dvd_right _ _
  have h3 : p ^ n + 1 ∣ (p ^ n) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (p ^ n) 1 (by decide : Odd 3)
  have hd : Nat.gcd 3 (p ^ n + 1) ∣ (p ^ n) ^ 3 * (((p ^ n) ^ 2 - 1) * ((p ^ n) ^ 3 + 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (h2.trans h3) _) _
  rw [h1, Nat.div_mul_cancel hd, mul_assoc]

theorem odd_gcd_three (a : ℕ) : Odd (Nat.gcd 3 a) := by
  rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 a) with h | h <;> rw [h] <;> decide

theorem fac2_mul {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).factorization 2 = x.factorization 2 + y.factorization 2 := by
  rw [Nat.factorization_mul hx hy]
  rfl

theorem fac2_odd {x : ℕ} (hx : Odd x) : x.factorization 2 = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h
  exact (Nat.not_even_iff_odd.mpr hx) (even_iff_two_dvd.mpr h)

theorem fac2_two_pow_mul {x : ℕ} (k : ℕ) (hx : x ≠ 0) :
    (2 ^ k * x).factorization 2 = x.factorization 2 + k := by
  rw [fac2_mul (pow_ne_zero _ (by norm_num)) hx, Nat.Prime.factorization_pow Nat.prime_two]
  simp [add_comm]

theorem fac2_mul_odd {x y : ℕ} (hx : x ≠ 0) (hy : Odd y) :
    (x * y).factorization 2 = x.factorization 2 := by
  rw [fac2_mul hx (Odd.pos hy).ne', fac2_odd hy, add_zero]

theorem key (s : ℕ) :
    ((2 * s + 1) ^ 2 - 1 = 2 ^ 2 * (s * (s + 1))) ∧
    ((2 * s + 1) ^ 3 - 1 = 2 ^ 1 * (s * (4 * s ^ 2 + 6 * s + 3))) ∧
    ((2 * s + 1) ^ 3 + 1 = 2 ^ 1 * ((s + 1) * (4 * s ^ 2 + 2 * s + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.sub_eq_of_eq_add
    ring
  · apply Nat.sub_eq_of_eq_add
    ring
  · ring

theorem fac2_of_mul {N c X : ℕ} (hc : Odd c) (hX : N * c = X) (hN : N ≠ 0) :
    N.factorization 2 = X.factorization 2 := by
  rw [← hX, fac2_mul_odd hN hc]

theorem fac2_q_add_one (s : ℕ) (hs : s + 1 ≠ 0) :
    (2 * s + 1 + 1).factorization 2 = (s + 1).factorization 2 + 1 := by
  have : 2 * s + 1 + 1 = 2 ^ 1 * (s + 1) := by ring
  rw [this, fac2_two_pow_mul 1 hs]

theorem fac2_q_sub_one (s : ℕ) (hs : s ≠ 0) :
    (2 * s + 1 - 1).factorization 2 = s.factorization 2 + 1 := by
  have : 2 * s + 1 - 1 = 2 ^ 1 * s := by rw [pow_one]; omega
  rw [this, fac2_two_pow_mul 1 hs]

theorem factorization_L3_sd {q N c : ℕ} (hq : q % 4 = 3) (hc : Odd c)
    (hN : N * c = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) :
    N.factorization 2 = (q + 1).factorization 2 + 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s + 1 := ⟨q / 2, by omega⟩
  have hsodd : Odd s := ⟨s / 2, by omega⟩
  have hs0 : s ≠ 0 := by omega
  have hs10 : s + 1 ≠ 0 := by omega
  obtain ⟨e2, e3, -⟩ := key s
  rw [e2, e3] at hN
  have hq3 : Odd ((2 * s + 1) ^ 3) := (odd_two_mul_add_one s).pow
  have hP : Odd (4 * s ^ 2 + 6 * s + 3) := ⟨2 * s ^ 2 + 3 * s + 1, by ring⟩
  have hNne : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    have h1 : (2 * s + 1) ^ 3 ≠ 0 := (Odd.pos hq3).ne'
    have h2 : (2 : ℕ) ^ 2 * (s * (s + 1)) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hs10)
    have h3 : (2 : ℕ) ^ 1 * (s * (4 * s ^ 2 + 6 * s + 3)) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero hs0 (Odd.pos hP).ne')
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hN.symm
  have e : (2 * s + 1) ^ 3 * (2 ^ 2 * (s * (s + 1))) * (2 ^ 1 * (s * (4 * s ^ 2 + 6 * s + 3)))
      = 2 ^ 3 * (((2 * s + 1) ^ 3 * (s * (s + 1)) * (s * (4 * s ^ 2 + 6 * s + 3)))) := by ring
  rw [fac2_of_mul hc hN hNne, e, fac2_two_pow_mul 3 (mul_ne_zero (mul_ne_zero (Odd.pos hq3).ne'
      (mul_ne_zero hs0 hs10)) (mul_ne_zero hs0 (Odd.pos hP).ne')),
    fac2_mul (mul_ne_zero (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10))
      (mul_ne_zero hs0 (Odd.pos hP).ne'),
    fac2_mul (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10), fac2_odd hq3, fac2_mul hs0 hs10,
    fac2_mul hs0 (Odd.pos hP).ne', fac2_odd hsodd, fac2_odd hP, fac2_q_add_one s hs10]
  omega

theorem factorization_L3_wr {q N c : ℕ} (hq : q % 4 = 1) (hq1 : 1 < q) (hc : Odd c)
    (hN : N * c = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) :
    N.factorization 2 = 2 * (q - 1).factorization 2 + 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s + 1 := ⟨q / 2, by omega⟩
  have hseven : Even s := ⟨s / 2, by omega⟩
  have hs0 : s ≠ 0 := by omega
  have hs10 : s + 1 ≠ 0 := by omega
  have hs1odd : Odd (s + 1) := hseven.add_one
  obtain ⟨e2, e3, -⟩ := key s
  rw [e2, e3] at hN
  have hq3 : Odd ((2 * s + 1) ^ 3) := (odd_two_mul_add_one s).pow
  have hP : Odd (4 * s ^ 2 + 6 * s + 3) := ⟨2 * s ^ 2 + 3 * s + 1, by ring⟩
  have hNne : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    have h1 : (2 * s + 1) ^ 3 ≠ 0 := (Odd.pos hq3).ne'
    have h2 : (2 : ℕ) ^ 2 * (s * (s + 1)) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hs10)
    have h3 : (2 : ℕ) ^ 1 * (s * (4 * s ^ 2 + 6 * s + 3)) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero hs0 (Odd.pos hP).ne')
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hN.symm
  have e : (2 * s + 1) ^ 3 * (2 ^ 2 * (s * (s + 1))) * (2 ^ 1 * (s * (4 * s ^ 2 + 6 * s + 3)))
      = 2 ^ 3 * (((2 * s + 1) ^ 3 * (s * (s + 1)) * (s * (4 * s ^ 2 + 6 * s + 3)))) := by ring
  rw [fac2_of_mul hc hN hNne, e, fac2_two_pow_mul 3 (mul_ne_zero (mul_ne_zero (Odd.pos hq3).ne'
      (mul_ne_zero hs0 hs10)) (mul_ne_zero hs0 (Odd.pos hP).ne')),
    fac2_mul (mul_ne_zero (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10))
      (mul_ne_zero hs0 (Odd.pos hP).ne'),
    fac2_mul (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10), fac2_odd hq3, fac2_mul hs0 hs10,
    fac2_mul hs0 (Odd.pos hP).ne', fac2_odd hs1odd, fac2_odd hP, fac2_q_sub_one s hs0]
  omega

theorem factorization_U3_wr {q N c : ℕ} (hq : q % 4 = 3) (hc : Odd c)
    (hN : N * c = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) :
    N.factorization 2 = 2 * (q + 1).factorization 2 + 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s + 1 := ⟨q / 2, by omega⟩
  have hsodd : Odd s := ⟨s / 2, by omega⟩
  have hs0 : s ≠ 0 := by omega
  have hs10 : s + 1 ≠ 0 := by omega
  obtain ⟨e2, -, e3⟩ := key s
  rw [e2, e3] at hN
  have hq3 : Odd ((2 * s + 1) ^ 3) := (odd_two_mul_add_one s).pow
  have hP : Odd (4 * s ^ 2 + 2 * s + 1) := ⟨2 * s ^ 2 + s, by ring⟩
  have hNne : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    have h1 : (2 * s + 1) ^ 3 ≠ 0 := (Odd.pos hq3).ne'
    have h2 : (2 : ℕ) ^ 2 * (s * (s + 1)) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hs10)
    have h3 : (2 : ℕ) ^ 1 * ((s + 1) * (4 * s ^ 2 + 2 * s + 1)) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero hs10 (Odd.pos hP).ne')
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hN.symm
  have e : (2 * s + 1) ^ 3 * (2 ^ 2 * (s * (s + 1))) *
      (2 ^ 1 * ((s + 1) * (4 * s ^ 2 + 2 * s + 1)))
      = 2 ^ 3 * (((2 * s + 1) ^ 3 * (s * (s + 1)) * ((s + 1) * (4 * s ^ 2 + 2 * s + 1)))) := by
    ring
  rw [fac2_of_mul hc hN hNne, e, fac2_two_pow_mul 3 (mul_ne_zero (mul_ne_zero (Odd.pos hq3).ne'
      (mul_ne_zero hs0 hs10)) (mul_ne_zero hs10 (Odd.pos hP).ne')),
    fac2_mul (mul_ne_zero (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10))
      (mul_ne_zero hs10 (Odd.pos hP).ne'),
    fac2_mul (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10), fac2_odd hq3, fac2_mul hs0 hs10,
    fac2_mul hs10 (Odd.pos hP).ne', fac2_odd hsodd, fac2_odd hP, fac2_q_add_one s hs10]
  omega

theorem factorization_U3_sd {q N c : ℕ} (hq : q % 4 = 1) (hq1 : 1 < q) (hc : Odd c)
    (hN : N * c = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) :
    N.factorization 2 = (q - 1).factorization 2 + 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = 2 * s + 1 := ⟨q / 2, by omega⟩
  have hseven : Even s := ⟨s / 2, by omega⟩
  have hs0 : s ≠ 0 := by omega
  have hs10 : s + 1 ≠ 0 := by omega
  have hs1odd : Odd (s + 1) := hseven.add_one
  obtain ⟨e2, -, e3⟩ := key s
  rw [e2, e3] at hN
  have hq3 : Odd ((2 * s + 1) ^ 3) := (odd_two_mul_add_one s).pow
  have hP : Odd (4 * s ^ 2 + 2 * s + 1) := ⟨2 * s ^ 2 + s, by ring⟩
  have hNne : N ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    have h1 : (2 * s + 1) ^ 3 ≠ 0 := (Odd.pos hq3).ne'
    have h2 : (2 : ℕ) ^ 2 * (s * (s + 1)) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hs10)
    have h3 : (2 : ℕ) ^ 1 * ((s + 1) * (4 * s ^ 2 + 2 * s + 1)) ≠ 0 :=
      mul_ne_zero (by norm_num) (mul_ne_zero hs10 (Odd.pos hP).ne')
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 hN.symm
  have e : (2 * s + 1) ^ 3 * (2 ^ 2 * (s * (s + 1))) *
      (2 ^ 1 * ((s + 1) * (4 * s ^ 2 + 2 * s + 1)))
      = 2 ^ 3 * (((2 * s + 1) ^ 3 * (s * (s + 1)) * ((s + 1) * (4 * s ^ 2 + 2 * s + 1)))) := by
    ring
  rw [fac2_of_mul hc hN hNne, e, fac2_two_pow_mul 3 (mul_ne_zero (mul_ne_zero (Odd.pos hq3).ne'
      (mul_ne_zero hs0 hs10)) (mul_ne_zero hs10 (Odd.pos hP).ne')),
    fac2_mul (mul_ne_zero (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10))
      (mul_ne_zero hs10 (Odd.pos hP).ne'),
    fac2_mul (Odd.pos hq3).ne' (mul_ne_zero hs0 hs10), fac2_odd hq3, fac2_mul hs0 hs10,
    fac2_mul hs10 (Odd.pos hP).ne', fac2_odd hs1odd, fac2_odd hP, fac2_q_sub_one s hs0]
  omega

end Lemma44bOrd

end CFSG.GH74.GLS.IVK.Proofs2
