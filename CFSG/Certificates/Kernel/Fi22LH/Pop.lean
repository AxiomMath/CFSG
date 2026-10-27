module

public import CFSG.Certificates.Kernel.Fi22LH.Bits
public import CFSG.Certificates.Kernel.Fi22LH.Lanes
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import CFSG.Certificates.Kernel.Fi22LH.Prim
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KC.Enum

@[expose] def cnt (x : Nat) : Nat → Nat → Nat
  | 0, j => (x.testBit j).toNat
  | s + 1, j => cnt x s (2 * j) + cnt x s (2 * j + 1)

theorem cnt_le (x : Nat) : ∀ s j, cnt x s j ≤ 2 ^ s
  | 0, j => by simp only [cnt]; cases x.testBit j <;> decide
  | s + 1, j => by
    simp only [cnt]
    have := cnt_le x s (2 * j)
    have := cnt_le x s (2 * j + 1)
    rw [Nat.pow_succ]
    omega

theorem sum_pairs (f : Nat → Nat) : ∀ n,
    ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) = ∑ j ∈ Finset.range (2 * n), f j
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_pairs f n, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_assoc]

theorem sum_cnt (x : Nat) : ∀ s n,
    ∑ j ∈ Finset.range n, cnt x s j = ∑ j ∈ Finset.range (2 ^ s * n), (x.testBit j).toNat
  | 0, n => by simp [cnt]
  | s + 1, n => by
    simp only [cnt]
    rw [sum_pairs (cnt x s) n, sum_cnt x s (2 * n), Nat.pow_succ]
    congr 2
    ring

theorem countP_range (p : Nat → Bool) : ∀ n,
    (List.range n).countP p = ∑ i ∈ Finset.range n, (p i).toNat
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.countP_append, countP_range p n, Finset.sum_range_succ]
    cases h : p n <;> simp [h]

theorem psum_eq_sum (f : Nat → Nat) (j : Nat) : ∀ m,
    psum f m j = ∑ t ∈ Finset.range m, if t ≤ j then f (j - t) else 0
  | 0 => rfl
  | m + 1 => by
    rw [psum, psum_eq_sum f j m, Finset.sum_range_succ]

theorem psum_top (f : Nat → Nat) (m : Nat) :
    psum f (m + 1) m = ∑ t ∈ Finset.range (m + 1), f t := by
  rw [psum_eq_sum, ← Finset.sum_range_reflect f (m + 1)]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [if_pos (by simp at ht; omega)]
  congr 1

theorem lanes_top {w : Nat} {f : Nat → Nat} {n : Nat} (hf : ∀ i < n + 1, f i < 2 ^ w) :
    lanes w f (n + 1) / 2 ^ (w * n) = f n := by
  rw [lanes_succ, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (lanes_lt n fun i hi => hf i (by omega)), Nat.add_zero]

theorem div_mod_pow (P a b : Nat) : P / 2 ^ a % 2 ^ b = P % 2 ^ (a + b) / 2 ^ a := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  by_cases h : q < b
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

theorem two_mul_lt (s : Nat) (hs : 2 ≤ s) : 2 ^ s + 2 ^ s < 2 ^ 2 ^ s := by
  have h1 : s + 1 < 2 ^ s := by
    induction s, hs using Nat.le_induction with
    | base => decide
    | succ s hs ih =>
      rw [Nat.pow_succ]
      omega
  rw [← Nat.two_mul, ← Nat.pow_succ']
  exact Nat.pow_lt_pow_right (by decide) h1

theorem cnt_pair_lt (x s : Nat) (hs : 2 ≤ s) (n i : Nat) :
    cnt x s i + (if i + 1 < n then cnt x s (i + 1) else 0) < 2 ^ 2 ^ s := by
  have h1 := cnt_le x s i
  have h2 := cnt_le x s (i + 1)
  have h3 := two_mul_lt s hs
  split <;> omega

theorem nsub_one (a : Nat) : Nat.sub a (nat_lit 1) = a - 1 := rfl

theorem rep_gen {W w n : Nat} (hw : 0 < w) (hn : w * n = W) (v : Nat) :
    Nat.mul v (Nat.div (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) = lanes w (fun _ => v) n := by
  rw [shiftLeft_one, shiftLeft_one, nsub_one, nsub_one, ← hn]
  change v * ((2 ^ (w * n) - 1) / (2 ^ w - 1)) = _
  rw [← lanes_ones_eq hw n, lanes_mul_const, lanes_congr fun i _ => Nat.mul_one v]

theorem rep_eq {w n : Nat} (hw : 0 < w) (hn : w * n = 3584) (v : Nat) :
    rep w v = lanes w (fun _ => v) n := by
  unfold rep
  exact rep_gen hw hn v

theorem rep_lt {w n : Nat} (hw : 0 < w) (hn : w * n = 3584) {v : Nat} (hv : v < 2 ^ w) :
    rep w v < 2 ^ 3584 := by
  rw [rep_eq hw hn, ← hn]
  exact lanes_lt n fun _ _ => hv

theorem testBit_rep {w n : Nat} (hw : 0 < w) (hn : w * n = 3584) {v : Nat} (hv : v < 2 ^ w)
    {p : Nat} (hp : 3584 ≤ p) : (rep w v).testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rep_lt hw hn hv) (Nat.pow_le_pow_right (by decide) hp))

theorem nlor_eq (a b : Nat) : Nat.lor a b = a ||| b := rfl

theorem nshl_eq (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl

theorem masks_eq : masks = Nat.lor (rep (nat_lit 2) (nat_lit 1))
    (Nat.lor (Nat.shiftLeft (rep (nat_lit 4) (nat_lit 3)) (nat_lit 3584))
    (Nat.lor (Nat.shiftLeft (rep (nat_lit 8) (nat_lit 15)) (nat_lit 7168))
    (Nat.lor (Nat.shiftLeft (rep (nat_lit 16) (nat_lit 255)) (nat_lit 10752))
    (Nat.lor (Nat.shiftLeft (rep (nat_lit 32) (nat_lit 65535)) (nat_lit 14336))
    (Nat.lor (Nat.shiftLeft (rep (nat_lit 64) (nat_lit 4294967295)) (nat_lit 17920))
      (Nat.shiftLeft (rep (nat_lit 64) (nat_lit 1)) (nat_lit 21504))))))) := by
  unfold masks
  rfl

theorem testBit_masks (q : Nat) : masks.testBit q =
    ((rep 2 1).testBit q || (decide (3584 ≤ q) && (rep 4 3).testBit (q - 3584)) ||
      (decide (7168 ≤ q) && (rep 8 15).testBit (q - 7168)) ||
      (decide (10752 ≤ q) && (rep 16 255).testBit (q - 10752)) ||
      (decide (14336 ≤ q) && (rep 32 65535).testBit (q - 14336)) ||
      (decide (17920 ≤ q) && (rep 64 4294967295).testBit (q - 17920)) ||
      (decide (21504 ≤ q) && (rep 64 1).testBit (q - 21504))) := by
  rw [masks_eq, nlor_eq, nlor_eq, nlor_eq, nlor_eq, nlor_eq, nlor_eq, nshl_eq, nshl_eq, nshl_eq,
    nshl_eq, nshl_eq, nshl_eq, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or, Nat.testBit_or,
    Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  simp only [Bool.or_assoc]

theorem mI_testBit (i q : Nat) :
    (mI masks i).testBit q = (decide (q < 3584) && masks.testBit (3584 * i + q)) := by
  unfold mI
  rw [shiftLeft_one, nsub_one, testBit_fld]
  rfl

theorem rep_lt' : (rep 2 1 < 2 ^ 3584) ∧ rep 4 3 < 2 ^ 3584 ∧ rep 8 15 < 2 ^ 3584 ∧
    rep 16 255 < 2 ^ 3584 ∧ rep 32 65535 < 2 ^ 3584 ∧ rep 64 4294967295 < 2 ^ 3584 ∧
    rep 64 1 < 2 ^ 3584 :=
  ⟨rep_lt (n := 1792) (by decide) (by decide) (by decide),
    rep_lt (n := 896) (by decide) (by decide) (by decide),
    rep_lt (n := 448) (by decide) (by decide) (by decide),
    rep_lt (n := 224) (by decide) (by decide) (by decide),
    rep_lt (n := 112) (by decide) (by decide) (by decide),
    rep_lt (n := 56) (by decide) (by decide) (by decide),
    rep_lt (n := 56) (by decide) (by decide) (by decide)⟩

theorem tb_ge {r : Nat} (hr : r < 2 ^ 3584) {p : Nat} (hp : 3584 ≤ p) : r.testBit p = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide) hp))

theorem mI_eq {i : Nat} {r : Nat} (hr : r < 2 ^ 3584)
    (h : ∀ q < 3584, masks.testBit (3584 * i + q) = r.testBit q) : mI masks i = r := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [mI_testBit]
  by_cases hq : q < 3584
  · rw [decide_eq_true hq, Bool.true_and, h q hq]
  · rw [decide_eq_false hq, Bool.false_and, tb_ge hr (by omega)]

theorem mI0 : mI masks (nat_lit 0) = rep 2 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h0 fun q hq => ?_
  rw [testBit_masks,
    decide_eq_false (show ¬ 3584 ≤ 3584 * 0 + q by omega),
    decide_eq_false (show ¬ 7168 ≤ 3584 * 0 + q by omega),
    decide_eq_false (show ¬ 10752 ≤ 3584 * 0 + q by omega),
    decide_eq_false (show ¬ 14336 ≤ 3584 * 0 + q by omega),
    decide_eq_false (show ¬ 17920 ≤ 3584 * 0 + q by omega),
    decide_eq_false (show ¬ 21504 ≤ 3584 * 0 + q by omega),
    show 3584 * 0 + q = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem mI1 : mI masks (nat_lit 1) = rep 4 3 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h1 fun q hq => ?_
  rw [testBit_masks,
    tb_ge h0 (show 3584 ≤ 3584 * 1 + q by omega),
    decide_eq_true (show 3584 ≤ 3584 * 1 + q by omega),
    decide_eq_false (show ¬ 7168 ≤ 3584 * 1 + q by omega),
    decide_eq_false (show ¬ 10752 ≤ 3584 * 1 + q by omega),
    decide_eq_false (show ¬ 14336 ≤ 3584 * 1 + q by omega),
    decide_eq_false (show ¬ 17920 ≤ 3584 * 1 + q by omega),
    decide_eq_false (show ¬ 21504 ≤ 3584 * 1 + q by omega),
    show 3584 * 1 + q - 3584 = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem mI2 : mI masks (nat_lit 2) = rep 8 15 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h2 fun q hq => ?_
  rw [testBit_masks,
    tb_ge h0 (show 3584 ≤ 3584 * 2 + q by omega),
    decide_eq_true (show 3584 ≤ 3584 * 2 + q by omega),
    tb_ge h1 (show 3584 ≤ 3584 * 2 + q - 3584 by omega),
    decide_eq_true (show 7168 ≤ 3584 * 2 + q by omega),
    decide_eq_false (show ¬ 10752 ≤ 3584 * 2 + q by omega),
    decide_eq_false (show ¬ 14336 ≤ 3584 * 2 + q by omega),
    decide_eq_false (show ¬ 17920 ≤ 3584 * 2 + q by omega),
    decide_eq_false (show ¬ 21504 ≤ 3584 * 2 + q by omega),
    show 3584 * 2 + q - 7168 = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem mI3 : mI masks (nat_lit 3) = rep 16 255 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h3 fun q hq => ?_
  rw [testBit_masks,
    tb_ge h0 (show 3584 ≤ 3584 * 3 + q by omega),
    decide_eq_true (show 3584 ≤ 3584 * 3 + q by omega),
    tb_ge h1 (show 3584 ≤ 3584 * 3 + q - 3584 by omega),
    decide_eq_true (show 7168 ≤ 3584 * 3 + q by omega),
    tb_ge h2 (show 3584 ≤ 3584 * 3 + q - 7168 by omega),
    decide_eq_true (show 10752 ≤ 3584 * 3 + q by omega),
    decide_eq_false (show ¬ 14336 ≤ 3584 * 3 + q by omega),
    decide_eq_false (show ¬ 17920 ≤ 3584 * 3 + q by omega),
    decide_eq_false (show ¬ 21504 ≤ 3584 * 3 + q by omega),
    show 3584 * 3 + q - 10752 = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem mI4 : mI masks (nat_lit 4) = rep 32 65535 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h4 fun q hq => ?_
  rw [testBit_masks,
    tb_ge h0 (show 3584 ≤ 3584 * 4 + q by omega),
    decide_eq_true (show 3584 ≤ 3584 * 4 + q by omega),
    tb_ge h1 (show 3584 ≤ 3584 * 4 + q - 3584 by omega),
    decide_eq_true (show 7168 ≤ 3584 * 4 + q by omega),
    tb_ge h2 (show 3584 ≤ 3584 * 4 + q - 7168 by omega),
    decide_eq_true (show 10752 ≤ 3584 * 4 + q by omega),
    tb_ge h3 (show 3584 ≤ 3584 * 4 + q - 10752 by omega),
    decide_eq_true (show 14336 ≤ 3584 * 4 + q by omega),
    decide_eq_false (show ¬ 17920 ≤ 3584 * 4 + q by omega),
    decide_eq_false (show ¬ 21504 ≤ 3584 * 4 + q by omega),
    show 3584 * 4 + q - 14336 = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem mI5 : mI masks (nat_lit 5) = rep 64 4294967295 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h5 fun q hq => ?_
  rw [testBit_masks,
    tb_ge h0 (show 3584 ≤ 3584 * 5 + q by omega),
    decide_eq_true (show 3584 ≤ 3584 * 5 + q by omega),
    tb_ge h1 (show 3584 ≤ 3584 * 5 + q - 3584 by omega),
    decide_eq_true (show 7168 ≤ 3584 * 5 + q by omega),
    tb_ge h2 (show 3584 ≤ 3584 * 5 + q - 7168 by omega),
    decide_eq_true (show 10752 ≤ 3584 * 5 + q by omega),
    tb_ge h3 (show 3584 ≤ 3584 * 5 + q - 10752 by omega),
    decide_eq_true (show 14336 ≤ 3584 * 5 + q by omega),
    tb_ge h4 (show 3584 ≤ 3584 * 5 + q - 14336 by omega),
    decide_eq_true (show 17920 ≤ 3584 * 5 + q by omega),
    decide_eq_false (show ¬ 21504 ≤ 3584 * 5 + q by omega),
    show 3584 * 5 + q - 17920 = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem mI6 : mI masks (nat_lit 6) = rep 64 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := rep_lt'
  refine mI_eq h6 fun q hq => ?_
  rw [testBit_masks,
    tb_ge h0 (show 3584 ≤ 3584 * 6 + q by omega),
    decide_eq_true (show 3584 ≤ 3584 * 6 + q by omega),
    tb_ge h1 (show 3584 ≤ 3584 * 6 + q - 3584 by omega),
    decide_eq_true (show 7168 ≤ 3584 * 6 + q by omega),
    tb_ge h2 (show 3584 ≤ 3584 * 6 + q - 7168 by omega),
    decide_eq_true (show 10752 ≤ 3584 * 6 + q by omega),
    tb_ge h3 (show 3584 ≤ 3584 * 6 + q - 10752 by omega),
    decide_eq_true (show 14336 ≤ 3584 * 6 + q by omega),
    tb_ge h4 (show 3584 ≤ 3584 * 6 + q - 14336 by omega),
    decide_eq_true (show 17920 ≤ 3584 * 6 + q by omega),
    tb_ge h5 (show 3584 ≤ 3584 * 6 + q - 17920 by omega),
    decide_eq_true (show 21504 ≤ 3584 * 6 + q by omega),
    show 3584 * 6 + q - 21504 = q by omega]
  simp only [Bool.false_or, Bool.or_false, Bool.true_and, Bool.false_and]

theorem final_sum {w n B : Nat} {c : Nat → Nat} (hc : ∀ i, c i ≤ B) (hB : (n + 1) * B < 2 ^ w) :
    lanes w c (n + 1) * lanes w (fun _ => 1) (n + 1) % 2 ^ (w * (n + 1)) / 2 ^ (w * n) =
      ∑ t ∈ Finset.range (n + 1), c t := by
  rw [lanes_mul_ones hc hB (n + 1) (le_refl _), lanes_top, psum_top]
  intro i _
  exact Nat.lt_of_le_of_lt (psum_le hc _ _) hB

theorem popK_eq {x : Nat} (hx : x < 2 ^ 3584) :
    popK masks x = (List.range 3584).countP fun i => x.testBit i := by
  have ha : Nat.sub x (Nat.land (Nat.shiftRight x (nat_lit 1)) (mI masks (nat_lit 0))) =
      lanes 2 (cnt x 1) 1792 := by
    rw [mI0, rep_eq (n := 1792) (by decide) (by decide)]
    exact pair_bits (n := 1792) (by rw [show 2 * 1792 = 3584 by rfl]; exact hx)
  have hb : Nat.add (Nat.land (lanes 2 (cnt x 1) 1792) (mI masks (nat_lit 1)))
      (Nat.land (Nat.shiftRight (lanes 2 (cnt x 1) 1792) (nat_lit 2)) (mI masks (nat_lit 1))) =
      lanes 4 (cnt x 2) 896 := by
    rw [mI1, rep_eq (n := 896) (by decide) (by decide)]
    exact pair_mask (w := 2) (n := 896) (by decide)
      (fun i _ => Nat.lt_of_le_of_lt (cnt_le x 1 i) (by decide))
  have hc : Nat.land (Nat.add (lanes 4 (cnt x 2) 896) (Nat.shiftRight (lanes 4 (cnt x 2) 896)
      (nat_lit 4))) (mI masks (nat_lit 2)) = lanes 8 (cnt x 3) 448 := by
    rw [mI2, rep_eq (n := 448) (by decide) (by decide)]
    exact pair_addShift (w := 4) (n := 448) (by decide) (fun i _ => cnt_pair_lt x 2 (by decide) _ i)
  have hd : Nat.land (Nat.add (lanes 8 (cnt x 3) 448) (Nat.shiftRight (lanes 8 (cnt x 3) 448)
      (nat_lit 8))) (mI masks (nat_lit 3)) = lanes 16 (cnt x 4) 224 := by
    rw [mI3, rep_eq (n := 224) (by decide) (by decide)]
    exact pair_addShift (w := 8) (n := 224) (by decide) (fun i _ => cnt_pair_lt x 3 (by decide) _ i)
  have he : Nat.land (Nat.add (lanes 16 (cnt x 4) 224) (Nat.shiftRight (lanes 16 (cnt x 4) 224)
      (nat_lit 16))) (mI masks (nat_lit 4)) = lanes 32 (cnt x 5) 112 := by
    rw [mI4, rep_eq (n := 112) (by decide) (by decide)]
    exact pair_addShift (w := 16) (n := 112) (by decide)
      (fun i _ => cnt_pair_lt x 4 (by decide) _ i)
  have hf : Nat.land (Nat.add (lanes 32 (cnt x 5) 112) (Nat.shiftRight (lanes 32 (cnt x 5) 112)
      (nat_lit 32))) (mI masks (nat_lit 5)) = lanes 64 (cnt x 6) 56 := by
    rw [mI5, rep_eq (n := 56) (by decide) (by decide)]
    exact pair_addShift (w := 32) (n := 56) (by decide)
      (fun i _ => cnt_pair_lt x 5 (by decide) _ i)
  unfold popK
  simp only [strictN_eq]
  rw [ha, hb, hc, hd, he, hf, mI6, rep_eq (n := 56) (by decide) (by decide)]
  change ((lanes 64 (cnt x 6) 56 * lanes 64 (fun _ => 1) 56) >>> 3520) &&& (2 ^ 64 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, div_mod_pow,
    show 3520 + 64 = 64 * (55 + 1) by rfl, show 3520 = 64 * 55 by rfl,
    final_sum (B := 64) (fun i => cnt_le x 6 i) (by decide), countP_range,
    show 55 + 1 = 56 by rfl, sum_cnt]
  rfl

theorem pop64_eq (x : UInt64) : pop64 x = ∑ t ∈ Finset.range 64, (x.toNat.testBit t).toNat := by
  have c1 : (0x5555555555555555 : UInt64).toNat = lanes 2 (fun _ => 1) 32 := by decide
  have c2 : (0x3333333333333333 : UInt64).toNat = lanes (2 * 2) (fun _ => 2 ^ 2 - 1) 16 := by
    decide
  have c3 : (0x0f0f0f0f0f0f0f0f : UInt64).toNat = lanes (2 * 4) (fun _ => 2 ^ 4 - 1) 8 := by
    decide
  have c4 : (0x0101010101010101 : UInt64).toNat = lanes 8 (fun _ => 1) (7 + 1) := by decide
  have hx := UInt64.toNat_lt x
  unfold pop64
  dsimp only
  generalize hX1 : x - ((x >>> (1 : UInt64)) &&& (0x5555555555555555 : UInt64)) = X1
  generalize hX2 : (X1 &&& (0x3333333333333333 : UInt64)) +
    ((X1 >>> (2 : UInt64)) &&& (0x3333333333333333 : UInt64)) = X2
  generalize hX3 : (X2 + (X2 >>> (4 : UInt64))) &&& (0x0f0f0f0f0f0f0f0f : UInt64) = X3
  have hsh : ∀ (a : UInt64) (s : Nat), s < 64 → (a >>> UInt64.ofNat s).toNat = a.toNat >>> s :=
    fun a s hs => by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : s < 2 ^ 64),
        Nat.mod_eq_of_lt hs]
  have e1 : X1.toNat = lanes 2 (cnt x.toNat 1) 32 := by
    have hm : ((x >>> (1 : UInt64)) &&& (0x5555555555555555 : UInt64)).toNat =
        (x.toNat >>> 1) &&& lanes 2 (fun _ => 1) 32 := by
      rw [UInt64.toNat_and, c1, show (1 : UInt64) = UInt64.ofNat 1 from rfl, hsh x 1 (by decide)]
    have hp := pair_bits (n := 32) (x := x.toNat) hx
    have hle : ((x >>> (1 : UInt64)) &&& (0x5555555555555555 : UInt64)) ≤ x := by
      rw [UInt64.le_iff_toNat_le, hm]
      exact Nat.le_trans Nat.and_le_left (Nat.shiftRight_le _ _)
    rw [← hX1, UInt64.toNat_sub_of_le _ _ hle, hm, hp]
    rfl
  have e2 : X2.toNat = lanes 4 (cnt x.toNat 2) 16 := by
    have hp := pair_mask (w := 2) (n := 16) (by decide)
      (fun i _ => Nat.lt_of_le_of_lt (cnt_le x.toNat 1 i) (by decide) : ∀ i < 2 * 16, cnt x.toNat 1 i < 2 ^ 2)
    rw [← hX2, UInt64.toNat_add, UInt64.toNat_and, UInt64.toNat_and,
      show (2 : UInt64) = UInt64.ofNat 2 from rfl, hsh X1 2 (by decide), c2, e1]
    rw [show (2 : Nat) * 16 = 32 from rfl] at hp
    rw [hp, Nat.mod_eq_of_lt (lanes_lt 16 fun i _ => Nat.lt_of_le_of_lt (Nat.add_le_add
      (cnt_le x.toNat 1 _) (cnt_le x.toNat 1 _)) (by decide))]
    rfl
  have e3 : X3.toNat = lanes 8 (cnt x.toNat 3) 8 := by
    have hg : ∀ i < 2 * 8, cnt x.toNat 2 i + (if i + 1 < 2 * 8 then cnt x.toNat 2 (i + 1) else 0) <
        2 ^ 4 := fun i _ => cnt_pair_lt x.toNat 2 (by decide) _ i
    have hp := pair_addShift (w := 4) (n := 8) (by decide) hg
    have hl := addShift_lt (w := 4) (n := 8) (by decide) hg
    rw [show (2 : Nat) * 8 = 16 from rfl] at hp hl
    rw [← hX3, UInt64.toNat_and, UInt64.toNat_add, show (4 : UInt64) = UInt64.ofNat 4 from rfl,
      hsh X2 4 (by decide), c3, e2, Nat.mod_eq_of_lt hl, hp]
    rfl
  rw [show (56 : UInt64) = UInt64.ofNat 56 from rfl, hsh _ 56 (by decide), UInt64.toNat_mul, e3, c4,
    Nat.shiftRight_eq_div_pow, show 56 = 8 * 7 by rfl, show (64 : Nat) = 8 * (7 + 1) by rfl,
    final_sum (B := 8) (fun i => cnt_le x.toNat 3 i) (by decide), show 7 + 1 = 8 by rfl, sum_cnt]
  rfl

theorem fold_add_sum (g : Nat → Nat) : ∀ n,
    Nat.fold n (fun w _ acc => acc + g w) 0 = ∑ w ∈ Finset.range n, g w
  | 0 => by rw [Nat.fold_zero, Finset.sum_range_zero]
  | n + 1 => by rw [Nat.fold_succ, fold_add_sum g n, Finset.sum_range_succ]

theorem sum_blocks (h : Nat → Nat) : ∀ n,
    ∑ w ∈ Finset.range n, ∑ t ∈ Finset.range 64, h (64 * w + t) = ∑ y ∈ Finset.range (64 * n), h y
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_blocks h n, Nat.mul_succ, Finset.sum_range_add]

theorem andPop_eq {A B : Bits} (hA : A.size = 55) (hB : B.size = 55) :
    andPop A B = (List.range 3520).countP fun y => bitAt A y && bitAt B y := by
  unfold andPop
  rw [fold_add_sum, countP_range, show 3520 = 64 * 55 by rfl, ← sum_blocks]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pop64_eq]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < 64 := Finset.mem_range.1 ht
  rw [bitAt_eq, bitAt_eq, show (64 * w + t) / 64 = w by omega, show (64 * w + t) % 64 = t by omega,
    UInt64.toNat_and, Nat.testBit_and]

end CFSG.KS.Fi22LH
