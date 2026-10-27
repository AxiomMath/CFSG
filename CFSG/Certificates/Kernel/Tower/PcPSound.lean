module

public import Certificates.Data.Kernel.Tower.PcP
public import Certificates.Data.Kernel.Tower.Chunk
public import CFSG.Certificates.Kernel.Tower.Cls14Sound

public section

namespace Certificates.KernelTower

open Finset

theorem bitsAt_sum (p : Nat → Bool) : ∀ k,
    bitsAt k p = ∑ j ∈ range k, cond (p j) 1 0 * 2 ^ (15 * j) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : bitsAt (k + 1) p =
        bitsAt k p + Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mul 15 k)) (p k) := rfl
    rw [e, ih, sum_range_succ]
    cases p k
    · simp
    · change _ + 1 <<< (15 * k) = _ + 1 * 2 ^ (15 * k)
      rw [Nat.shiftLeft_eq]

theorem cntPI_sum (k : Nat) (iv : Nat → Bool) (q : Nat → Nat → Bool) : ∀ n,
    cntPI n k iv q = ∑ j ∈ range k, cntB n (fun c => iv c && q c j) * 2 ^ (15 * j) := by
  intro n
  induction n with
  | zero => simp [cntPI, cntB]
  | succ n ih =>
    have e : cntPI (n + 1) k iv q =
        cntPI n k iv q + Bool.rec (motive := fun _ => Nat) 0 (bitsAt k (q n)) (iv n) := rfl
    have e2 : ∀ j, cntB (n + 1) (fun c => iv c && q c j) =
        cond (iv n && q n j) 1 0 + cntB n (fun c => iv c && q c j) := fun j => rfl
    rw [e, ih]
    simp only [e2, add_mul, sum_add_distrib]
    rw [Nat.add_comm]
    congr 1
    cases iv n
    · simp
    · rw [bitsAt_sum]
      simp

theorem digit15_lt (D : Nat → Nat) (hD : ∀ j, D j < 32768) : ∀ k,
    ∑ j ∈ range k, D j * 2 ^ (15 * j) < 2 ^ (15 * k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have e : 2 ^ (15 * (k + 1)) = 32768 * 2 ^ (15 * k) := by
      rw [Nat.mul_succ, pow_add]
      ring
    have h1 : D k * 2 ^ (15 * k) ≤ 32767 * 2 ^ (15 * k) :=
      Nat.mul_le_mul_right _ (by have := hD k; omega)
    rw [e]
    omega

theorem digit15 (D : Nat → Nat) (hD : ∀ j, D j < 32768) : ∀ k, ∀ i < k,
    (∑ j ∈ range k, D j * 2 ^ (15 * j)) / 2 ^ (15 * i) % 32768 = D i := by
  intro k
  induction k with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro i hi
    rw [sum_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have e : 2 ^ (15 * k) = 2 ^ (15 * i) * (32768 * 2 ^ (15 * (k - i - 1))) := by
        rw [show (32768 : Nat) = 2 ^ 15 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
      rw [e, ← Nat.mul_assoc, Nat.mul_comm (D k), Nat.mul_assoc, Nat.add_mul_div_left _ _
        (by positivity), ← Nat.mul_assoc, Nat.mul_comm (D k), Nat.mul_assoc,
        Nat.add_mul_mod_self_left]
      exact ih i hi
    · rw [Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (digit15_lt D hD i), Nat.zero_add, Nat.mod_eq_of_lt (hD i)]

theorem cntPI_lane {n k : Nat} (iv : Nat → Bool) (q : Nat → Nat → Bool) (hn : n < 32768) {j : Nat}
    (hj : j < k) : lane (cntPI n k iv q) 15 32767 j = cntB n (fun c => iv c && q c j) := by
  rw [cls16_lane, cntPI_sum]
  have h := digit15 (fun j => if j < k then cntB n (fun c => iv c && q c j) else 0)
    (fun j => by
      split_ifs
      · exact Nat.lt_of_le_of_lt (cls16_cntB_le _ n) hn
      · omega) k j hj
  rw [if_pos hj] at h
  rw [← h]
  congr 2
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [if_pos hi]

theorem pcP_pcB {n : Nat} {mul : Nat → Nat → Nat} {OT LB RP CZ nl t x0 : Nat} (hn : n < 32768)
    (h : pcP n mul OT LB RP CZ nl t x0 = true) : pcB n mul OT LB RP CZ nl t x0 = true := by
  rw [pcP, pcFin, Bool.and_eq_true] at h
  obtain ⟨hS, hA⟩ := h
  generalize pcSL OT LB RP CZ t x0 nl = SL at hS hA
  generalize pcK OT LB RP CZ t x0 nl = k at hS hA
  rw [pcB, allB_true_iff]
  intro l hl
  have hSl := allB_true_iff.1 hS l hl
  rw [pcSel] at hSl
  cases ht : Nat.beq l (lbL LB t)
  · cases hx : Nat.beq l (lbL LB x0)
    · cases h1 : Nat.beq (oe OT (l16 RP l)) 1
      · simp
      · cases h2 : Nat.beq (lane CZ 15 32767 l) 64
        · simp
        · rw [ht, hx, h1, h2] at hSl
          simp only [Bool.or_false, Bool.not_false, Bool.and_true, Bool.not_true,
            Bool.false_or] at hSl
          obtain ⟨j, hj, hjl⟩ := anyB_eq_true.1 hSl
          have e := Nat.eq_of_beq_eq_true hjl
          have hAj := allB_true_iff.1 hA j hj
          rw [cntPI_lane _ _ hn hj] at hAj
          have hninv : ninvC n mul OT (l16 RP l) =
              cntB n (fun c => Nat.beq (oe OT c) 1 && pcC mul RP SL c j) := by
            simp only [ninvC, pcC, e]
          rw [hninv]
          revert hAj
          cases Nat.beq (cntB n (fun c => Nat.beq (oe OT c) 1 && pcC mul RP SL c j)) 87 <;> simp
    · simp
  · simp

end Certificates.KernelTower
