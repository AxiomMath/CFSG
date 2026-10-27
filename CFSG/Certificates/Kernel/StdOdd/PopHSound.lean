module

public import Certificates.Data.Kernel.StdOdd.PopH
public import CFSG.Certificates.Kernel.StdOdd.ChainSound

public section

namespace CFSG.KS.StdOdd.Chain

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit

theorem card_filter_eq_sum (n : ℕ) (x : ℕ) :
    ((Finset.range n).filter fun j => x.testBit j = true).card =
      ∑ j ∈ Finset.range n, if x.testBit j = true then 1 else 0 := by
  rw [Finset.card_filter]

theorem popH_eq : ∀ (d x : ℕ),
    popH d x = ((Finset.range (2 ^ d)).filter fun j => x.testBit j = true).card
  | 0, x => by
    change x &&& 1 = _
    rw [card_filter_eq_sum, pow_zero, Finset.sum_range_one, Nat.and_one_is_mod, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
  | d + 1, x => by
    change Bool.rec (motive := fun _ => ℕ)
      (forceN (Nat.shiftLeft 1 d) fun sh =>
        forceN (Nat.land x (Nat.sub (Nat.shiftLeft 1 sh) 1)) fun lo =>
        forceN (Nat.shiftRight x sh) fun hi => Nat.add (popH d lo) (popH d hi))
      0 (Nat.beq x 0) = _
    by_cases hx : x = 0
    · subst hx
      simp [Nat.zero_testBit]
    · rw [beq_false_of_ne' hx]
      change forceN (Nat.shiftLeft 1 d) (fun sh =>
        forceN (Nat.land x (Nat.sub (Nat.shiftLeft 1 sh) 1)) fun lo =>
        forceN (Nat.shiftRight x sh) fun hi => Nat.add (popH d lo) (popH d hi)) = _
      rw [forceN_eq, forceN_eq, forceN_eq, popH_eq d, popH_eq d]
      change ((Finset.range (2 ^ d)).filter fun j => (x &&& (1 <<< (1 <<< d) - 1)).testBit j = true).card
        + ((Finset.range (2 ^ d)).filter fun j => (x >>> (1 <<< d)).testBit j = true).card = _
      rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, card_filter_eq_sum,
        card_filter_eq_sum, card_filter_eq_sum, pow_succ, Nat.mul_two, Finset.sum_range_add]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Nat.testBit_mod_two_pow, decide_eq_true (Finset.mem_range.1 hj), Bool.true_and]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem popK_of_count : ∀ (c x n : ℕ), x < 2 ^ n →
    ((Finset.range n).filter fun j => x.testBit j = true).card = c → popK x c = true
  | 0, x, n, hn, h => by
    have hx : x = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.zero_testBit]
      by_cases hj : j < n
      · cases e : x.testBit j
        · rfl
        · have : j ∈ (Finset.range n).filter fun j => x.testBit j = true := by simp [hj, e]
          rw [Finset.card_eq_zero.1 h] at this
          cases this
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn
          (Nat.pow_le_pow_right (by omega) (by omega)))
    subst hx
    rfl
  | c + 1, x, n, hn, h => by
    change andB (notB (Nat.beq x 0)) (forceB (x &&& (x - 1)) fun y => popK y c) = true
    rw [andB_eq, Bool.and_eq_true, forceB_eq, notB_eq]
    have hx : x ≠ 0 := by
      rintro rfl
      simp [Nat.zero_testBit] at h
    obtain ⟨t, ht, e⟩ := land_sub_one x hx
    refine ⟨by rw [beq_false_of_ne' hx]; rfl, ?_⟩
    rw [e]
    have htn : 2 ^ t < 2 ^ n := by
      by_contra hc
      have : x < 2 ^ t := Nat.lt_of_lt_of_le hn (by omega)
      rw [Nat.testBit_lt_two_pow this] at ht
      cases ht
    refine popK_of_count c _ n (Nat.xor_lt_two_pow hn htn) ?_
    have := card_filter_xor ht hn
    omega

theorem popK_of_popHB {d x c : ℕ} (h : popHB d x c = true) : popK x c = true := by
  unfold popHB at h
  rw [andB_eq, Bool.and_eq_true] at h
  have hx : x < 2 ^ 2 ^ d := by
    have h0 : x >>> (1 <<< d) = 0 := Nat.eq_of_beq_eq_true h.1
    rw [Nat.shiftRight_eq_div_pow, Nat.one_shiftLeft, Nat.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.two_pow_pos _).ne'
    · exact h0
  exact popK_of_count c x _ hx ((popH_eq d x).symm.trans (Nat.eq_of_beq_eq_true h.2))

end CFSG.KS.StdOdd.Chain
