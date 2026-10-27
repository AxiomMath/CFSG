module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneSpr
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Ln

set_option exponentiation.threshold 140000

open CFSG.KC.BM CFSG.KC.BM.Dy

@[expose] def KKOK (KK : List (List ℕ)) (l : ℕ) : Prop :=
  ∀ l' < l, nthLL KK (l' + 1) = lnKs (16 * 2 ^ l') (2 * (16 * 2 ^ l'))

theorem lnT_succ (KK : List (List ℕ)) (U : ℕ → ℕ) (l i : ℕ) :
    lnT KK U (l + 1) i = lnQ (nthLL KK (l + 1)) (16 * 2 ^ l) (lnT KK U l i) (lnT KK U l (i + 2 ^ l)) := by
  change lnQ (nthLL KK (Nat.succ l)) (Nat.shiftLeft (nat_lit 16) l) (lnT KK U l i)
    (lnT KK U l (Nat.add i (Nat.shiftLeft (nat_lit 1) l))) = _
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul]
  rfl

theorem lnQ_eq (Ks : List ℕ) (w a b : ℕ) :
    lnQ Ks w a b = lnSpr Ks (lnD w (2 * w)) a + (lnSpr Ks (lnD w (2 * w)) b <<< w) := rfl

theorem lt_of_testBit_ge {x N : ℕ} (h : ∀ i, N ≤ i → x.testBit i = false) : x < 2 ^ N :=
  Nat.lt_pow_two_of_testBit x (fun i hi => h i hi)

theorem pair_bits {l : ℕ} {a b i : ℕ} {U : ℕ → ℕ}
    (hta : ∀ p, a.testBit p = (U (i + p / 16 % 2 ^ l)).testBit (16 * (p / 16 / 2 ^ l) + p % 16))
    (htb : ∀ p, b.testBit p =
      (U (i + 2 ^ l + p / 16 % 2 ^ l)).testBit (16 * (p / 16 / 2 ^ l) + p % 16))
    (k s : ℕ) (hs : s < 2 * (16 * 2 ^ l)) :
    (lay a (16 * 2 ^ l) (2 * (16 * 2 ^ l)) (2 * (16 * 2 ^ l) * k + s) ||
      (decide (16 * 2 ^ l ≤ 2 * (16 * 2 ^ l) * k + s) &&
        lay b (16 * 2 ^ l) (2 * (16 * 2 ^ l)) (2 * (16 * 2 ^ l) * k + s - 16 * 2 ^ l))) =
    (U (i + (2 * (16 * 2 ^ l) * k + s) / 16 % 2 ^ (l + 1))).testBit
      (16 * ((2 * (16 * 2 ^ l) * k + s) / 16 / 2 ^ (l + 1)) + (2 * (16 * 2 ^ l) * k + s) % 16) := by
  have hP : 2 * (16 * 2 ^ l) * k + s = 16 * (2 ^ (l + 1) * k) + s := by rw [pow_succ]; ring
  have hs16 : s / 16 < 2 ^ (l + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by decide), pow_succ]
    omega
  have hq : (2 * (16 * 2 ^ l) * k + s) / 16 = 2 ^ (l + 1) * k + s / 16 := by
    rw [hP, Nat.mul_add_div (by decide)]
  have hm1 : (2 * (16 * 2 ^ l) * k + s) / 16 % 2 ^ (l + 1) = s / 16 := by
    rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hs16]
  have hd1 : (2 * (16 * 2 ^ l) * k + s) / 16 / 2 ^ (l + 1) = k := by
    rw [hq, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hs16, Nat.add_zero]
  have hp16 : (2 * (16 * 2 ^ l) * k + s) % 16 = s % 16 := by
    rw [hP, Nat.mul_add_mod]
  rw [hm1, hd1, hp16]
  unfold lay
  obtain ⟨f1, f2⟩ := div_mod_of (rfl : 2 * (16 * 2 ^ l) * k + s = 2 * (16 * 2 ^ l) * k + s) hs
  rw [f1, f2]
  rcases Nat.lt_or_ge s (16 * 2 ^ l) with hsw | hsw
  ·
    have hb0 : (decide (16 * 2 ^ l ≤ 2 * (16 * 2 ^ l) * k + s) &&
        (decide ((2 * (16 * 2 ^ l) * k + s - 16 * 2 ^ l) % (2 * (16 * 2 ^ l)) < 16 * 2 ^ l) &&
          b.testBit ((2 * (16 * 2 ^ l) * k + s - 16 * 2 ^ l) / (2 * (16 * 2 ^ l)) * (16 * 2 ^ l) +
            (2 * (16 * 2 ^ l) * k + s - 16 * 2 ^ l) % (2 * (16 * 2 ^ l))))) = false := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp [show ¬ 16 * 2 ^ l ≤ s by omega]
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have e : 2 * (16 * 2 ^ l) * (k' + 1) + s - 16 * 2 ^ l =
            2 * (16 * 2 ^ l) * k' + (s + 16 * 2 ^ l) := by
          rw [Nat.mul_succ]
          omega
        rw [e, (div_mod_of rfl (by omega : s + 16 * 2 ^ l < 2 * (16 * 2 ^ l))).2]
        simp
    rw [hb0, Bool.or_false, decide_eq_true hsw, Bool.true_and, hta]
    have hs16' : s / 16 < 2 ^ l := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      omega
    have e1 : (k * (16 * 2 ^ l) + s) / 16 = 2 ^ l * k + s / 16 := by
      rw [show k * (16 * 2 ^ l) + s = 16 * (2 ^ l * k) + s by ring, Nat.mul_add_div (by decide)]
    rw [e1, Nat.mul_add_mod, Nat.mod_eq_of_lt hs16', Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hs16', Nat.add_zero,
      show (k * (16 * 2 ^ l) + s) % 16 = s % 16 by
        rw [show k * (16 * 2 ^ l) + s = 16 * (2 ^ l * k) + s by ring, Nat.mul_add_mod]]
  ·
    obtain ⟨r, rfl⟩ : ∃ r, s = 16 * 2 ^ l + r := ⟨s - 16 * 2 ^ l, by omega⟩
    have hrw : r < 16 * 2 ^ l := by omega
    rw [decide_eq_false (by omega : ¬ 16 * 2 ^ l + r < 16 * 2 ^ l), Bool.false_and, Bool.false_or,
      decide_eq_true (by omega : 16 * 2 ^ l ≤ 2 * (16 * 2 ^ l) * k + (16 * 2 ^ l + r)), Bool.true_and]
    have e : 2 * (16 * 2 ^ l) * k + (16 * 2 ^ l + r) - 16 * 2 ^ l = 2 * (16 * 2 ^ l) * k + r := by omega
    obtain ⟨g1, g2⟩ := div_mod_of (rfl : 2 * (16 * 2 ^ l) * k + r = 2 * (16 * 2 ^ l) * k + r) (by omega)
    rw [e, g1, g2, decide_eq_true hrw, Bool.true_and, htb]
    have hr16 : r / 16 < 2 ^ l := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      omega
    have e1 : (k * (16 * 2 ^ l) + r) / 16 = 2 ^ l * k + r / 16 := by
      rw [show k * (16 * 2 ^ l) + r = 16 * (2 ^ l * k) + r by ring, Nat.mul_add_div (by decide)]
    have hsr : (16 * 2 ^ l + r) / 16 = 2 ^ l + r / 16 := by
      rw [Nat.mul_add_div (by decide)]
    rw [e1, Nat.mul_add_mod, Nat.mod_eq_of_lt hr16, Nat.mul_add_div (by positivity),
      Nat.div_eq_of_lt hr16, Nat.add_zero, hsr, Nat.add_assoc,
      show (k * (16 * 2 ^ l) + r) % 16 = (16 * 2 ^ l + r) % 16 by
        rw [show k * (16 * 2 ^ l) + r = 16 * (2 ^ l * k) + r by ring, Nat.mul_add_mod, Nat.mul_add_mod]]

theorem testBit_lnT {KK : List (List ℕ)} {U : ℕ → ℕ} :
    ∀ (l : ℕ), KKOK KK l → ∀ i, (∀ t < 2 ^ l, U (i + t) < 2 ^ (16 * 8192)) →
      lnT KK U l i < 2 ^ (8192 * (16 * 2 ^ l)) ∧
      ∀ p, (lnT KK U l i).testBit p =
        (U (i + p / 16 % 2 ^ l)).testBit (16 * (p / 16 / 2 ^ l) + p % 16)
  | 0, _, i, hU => by
    refine ⟨?_, fun p => ?_⟩
    · have := hU 0 (by decide)
      rw [Nat.add_zero] at this
      change U i < _
      simpa [Nat.mul_comm] using this
    · change (U i).testBit p = _
      simp only [pow_zero, Nat.mod_one, Nat.add_zero, Nat.div_one]
      rw [Nat.div_add_mod]
  | l + 1, hK, i, hU => by
    have hK' : KKOK KK l := fun l' hl' => hK l' (by omega)
    have h2 : (2 : ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by rw [pow_succ]; ring
    obtain ⟨ha, hta⟩ := testBit_lnT l hK' i (fun t ht => hU t (by omega))
    obtain ⟨hb, htb⟩ := testBit_lnT l hK' (i + 2 ^ l) (fun t ht => by
      rw [Nat.add_assoc]
      exact hU _ (by omega))
    have hw0 : 0 < 16 * 2 ^ l := by positivity
    rw [lnT_succ, hK l (by omega), lnQ_eq]
    have hsa := testBit_spr (W := 2 * (16 * 2 ^ l)) (by omega) hw0 ha
    have hsb := testBit_spr (W := 2 * (16 * 2 ^ l)) (by omega) hw0 hb
    have hA : ∀ p, (lnSpr (lnKs (16 * 2 ^ l) (2 * (16 * 2 ^ l))) (lnD (16 * 2 ^ l) (2 * (16 * 2 ^ l)))
        (lnT KK U l i)).testBit p = true → p % (2 * (16 * 2 ^ l)) < 16 * 2 ^ l := fun p h => by
      rw [hsa] at h
      unfold lay at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    have hB : ∀ p, ((lnSpr (lnKs (16 * 2 ^ l) (2 * (16 * 2 ^ l))) (lnD (16 * 2 ^ l) (2 * (16 * 2 ^ l)))
        (lnT KK U l (i + 2 ^ l))) <<< (16 * 2 ^ l)).testBit p = true →
        16 * 2 ^ l ≤ p % (2 * (16 * 2 ^ l)) := fun p h => by
      rw [Nat.testBit_shiftLeft, hsb] at h
      unfold lay at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, h2, -⟩ := h
      have hq := Nat.div_add_mod (p - 16 * 2 ^ l) (2 * (16 * 2 ^ l))
      have e : p = 2 * (16 * 2 ^ l) * ((p - 16 * 2 ^ l) / (2 * (16 * 2 ^ l))) +
          ((p - 16 * 2 ^ l) % (2 * (16 * 2 ^ l)) + 16 * 2 ^ l) := by omega
      rw [(div_mod_of e (by omega)).2]
      omega
    have key : ∀ p, (lnSpr (lnKs (16 * 2 ^ l) (2 * (16 * 2 ^ l))) (lnD (16 * 2 ^ l) (2 * (16 * 2 ^ l)))
        (lnT KK U l i) + (lnSpr (lnKs (16 * 2 ^ l) (2 * (16 * 2 ^ l)))
          (lnD (16 * 2 ^ l) (2 * (16 * 2 ^ l))) (lnT KK U l (i + 2 ^ l)) <<< (16 * 2 ^ l))).testBit p =
        (U (i + p / 16 % 2 ^ (l + 1))).testBit (16 * (p / 16 / 2 ^ (l + 1)) + p % 16) := by
      intro p
      rw [testBit_add_of_and (fun p hp => by
        have := hA p hp.1
        have := hB p hp.2
        omega), hsa, Nat.testBit_shiftLeft, hsb]
      have hq := Nat.div_add_mod p (2 * (16 * 2 ^ l))
      have hs := Nat.mod_lt p (by omega : 0 < 2 * (16 * 2 ^ l))
      rw [← hq]
      exact pair_bits hta htb _ _ hs
    refine ⟨lt_of_testBit_ge (fun p hp => ?_), key⟩
    rw [key]
    have h2' : 8192 ≤ p / 16 / 2 ^ (l + 1) := by
      rw [Nat.le_div_iff_mul_le (by positivity), Nat.le_div_iff_mul_le (by decide)]
      calc 8192 * 2 ^ (l + 1) * 16 = 8192 * (16 * 2 ^ (l + 1)) := by ring
        _ ≤ p := hp
    exact testBit_x_ge (hU _ (Nat.mod_lt _ (by positivity))) (by omega)

theorem fld_lnT4 {KK : List (List ℕ)} {U : ℕ → ℕ} (hK : KKOK KK 4) {i : ℕ}
    (hU : ∀ t < 16, U (i + t) < 2 ^ (16 * 8192)) {t : ℕ} (ht : t < 16) (k : ℕ) :
    fld (lnT KK U 4 i) (16 * k + t) = fld (U (i + t)) k := by
  obtain ⟨-, h⟩ := testBit_lnT 4 hK i hU
  apply Nat.eq_of_testBit_eq
  intro r
  rw [fld_testBit, fld_testBit, h]
  by_cases hr : r < 16
  · have e1 : (16 * (16 * k + t) + r) / 16 = 16 * k + t := by
      rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hr, Nat.add_zero]
    have e2 : (16 * (16 * k + t) + r) % 16 = r := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rw [e1, e2, show (2 : ℕ) ^ 4 = 16 from rfl, Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
      Nat.mul_add_div (by decide), Nat.div_eq_of_lt ht, Nat.add_zero]
  · simp [hr]

theorem lnT4_lt {KK : List (List ℕ)} {U : ℕ → ℕ} (hK : KKOK KK 4) {i : ℕ}
    (hU : ∀ t < 16, U (i + t) < 2 ^ (16 * 8192)) : lnT KK U 4 i < 2 ^ (16 * (16 * 8192)) := by
  have := (testBit_lnT 4 hK i hU).1
  rw [show 8192 * (16 * 2 ^ 4) = 16 * (16 * 8192) by norm_num] at this
  exact this

end CFSG.KC.BM.Ln

end
