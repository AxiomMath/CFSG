module

public import Certificates.Data.Kernel.O8.SBCenL
public import Certificates.Data.Kernel.O8.SB
public import CFSG.Certificates.Kernel.O8.SBCenSound
public import CFSG.Certificates.Kernel.AxisPlane.Pop

public section

namespace CFSG.KC.SBCenL

open CFSG.KC.Enum CFSG.KC.SB CFSG.KC.SBCen CFSG.KC.AxisPlane

theorem nl_and (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem nl_or (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem nl_xor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
theorem nl_shr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem nl_mod (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem lanesK_eq (f : ℕ → ℕ) : ∀ n, lanesK f n = lanes 7 f n
  | 0 => rfl
  | n + 1 => by
    change Nat.add (lanesK f n) (Nat.shiftLeft (f n) (Nat.mul 7 n)) = _
    rw [lanesK_eq f n, lanes, cen_shl, Nat.add_eq, Nat.mul_eq]
    ring

theorem small_tb {v k j : ℕ} (hv : v < 2 ^ k) (hj : k ≤ j) : v.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))

theorem tb127 (j : ℕ) : (127 : ℕ).testBit j = decide (j < 7) := Nat.testBit_two_pow_sub_one 7 j

theorem tb1 (j : ℕ) : (1 : ℕ).testBit j = decide (j < 1) := Nat.testBit_two_pow_sub_one 1 j

theorem tb_lanes {f : ℕ → ℕ} (hf : ∀ e < 128, f e < 128) (i : ℕ) :
    (lanes 7 f 128).testBit i = (decide (i < 7 * 128) && (f (i / 7)).testBit (i % 7)) :=
  testBit_lanes (by norm_num) 128 hf i

theorem ln_lanes {f : ℕ → ℕ} (hf : ∀ e < 128, f e < 128) {k : ℕ} (hk : k < 128) :
    (lanes 7 f 128 >>> (7 * k)) &&& 127 = f k := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftRight, tb_lanes hf, tb127]
  by_cases hj : j < 7
  · have e1 : (7 * k + j) / 7 = k := by omega
    have e2 : (7 * k + j) % 7 = j := by omega
    rw [e1, e2, decide_eq_true (by omega : 7 * k + j < 7 * 128), decide_eq_true hj]
    simp
  · rw [decide_eq_false hj, Bool.and_false]
    exact (small_tb (k := 7) (hf k hk) (by omega)).symm

theorem ln_lt (X s : ℕ) : (X >>> s) &&& 127 < 128 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem xor_lt {x y : ℕ} (hx : x < 128) (hy : y < 128) : x ^^^ y < 128 := by
  have h := Nat.xor_lt_two_pow (n := 7) (by simpa using hx) (by simpa using hy)
  simpa using h

theorem ln_xor (X Y s : ℕ) :
    ((X ^^^ Y) >>> s) &&& 127 = ((X >>> s) &&& 127) ^^^ ((Y >>> s) &&& 127) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases X.testBit (s + j) <;> cases Y.testBit (s + j) <;> simp

theorem ln_IDX {e : ℕ} (he : e < 128) : (IDX >>> (7 * e)) &&& 127 = e := by
  rw [IDX, lanesK_eq]
  exact ln_lanes (f := fun e => e) (fun e he => he) he

theorem lanes_cmul (w v : ℕ) (f : ℕ → ℕ) : ∀ n, v * lanes w f n = lanes w (fun e => v * f e) n
  | 0 => by simp [lanes]
  | n + 1 => by
    simp only [lanes]
    rw [← lanes_cmul w v f n]
    ring

theorem ln_RU {v e : ℕ} (hv : v < 128) (he : e < 128) : ((v * RU) >>> (7 * e)) &&& 127 = v := by
  rw [RU, lanesK_eq, lanes_cmul]
  exact ln_lanes (f := fun _ => v * 1) (fun _ _ => by omega) he |>.trans (Nat.mul_one v)

@[expose] def flg (p : ℕ → Bool) : ℕ := lanes 7 (fun e => if p e = true then 64 else 0) 128

theorem flg_lt (p : ℕ → Bool) : ∀ e < 128, (if p e = true then 64 else 0) < 128 := by
  intro e _
  split <;> norm_num

theorem tb_flg (p : ℕ → Bool) (i : ℕ) :
    (flg p).testBit i = (decide (i < 7 * 128) && (decide (i % 7 = 6) && p (i / 7))) := by
  unfold flg
  rw [tb_lanes (f := fun e => if p e = true then 64 else 0) (flg_lt p)]
  have hr : i % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have h64 : ∀ r < 7, (64 : ℕ).testBit r = decide (r = 6) := by decide
  generalize i % 7 = r at hr ⊢
  cases p (i / 7)
  · simp
  · simp [h64 r hr]

theorem flg_congr {p q : ℕ → Bool} (h : ∀ e < 128, p e = q e) : flg p = flg q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [tb_flg, tb_flg]
  rcases Nat.lt_or_ge i (7 * 128) with hi | hi
  · rw [h (i / 7) (by omega)]
  · simp [show ¬ i < 7 * 128 by omega]

theorem flg_false {p : ℕ → Bool} (h : ∀ e < 128, p e = false) : flg p = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [tb_flg, Nat.zero_testBit]
  rcases Nat.lt_or_ge i (7 * 128) with hi | hi
  · simp [h (i / 7) (by omega)]
  · simp [show ¬ i < 7 * 128 by omega]

theorem flg_and (p q : ℕ → Bool) : flg p &&& flg q = flg fun e => p e && q e := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, tb_flg, tb_flg, tb_flg]
  cases decide (i < 7 * 128) <;> cases decide (i % 7 = 6) <;> cases p (i / 7) <;> cases q (i / 7) <;>
    rfl

theorem flg_xor (p q : ℕ → Bool) : flg p ^^^ flg q = flg fun e => Bool.xor (p e) (q e) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, tb_flg, tb_flg, tb_flg]
  cases decide (i < 7 * 128) <;> cases decide (i % 7 = 6) <;> cases p (i / 7) <;> cases q (i / 7) <;>
    rfl

theorem flg_64 : (64 : ℕ) = flg fun e => decide (e = 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (64 : ℕ) = 2 ^ 6 from rfl, Nat.testBit_two_pow, tb_flg]
  by_cases h : i = 6
  · subst h
    decide
  · rw [decide_eq_false (Ne.symm h)]
    by_cases h2 : i % 7 = 6
    · rw [decide_eq_true h2, decide_eq_false (show ¬ i / 7 = 0 by omega), Bool.and_false, Bool.and_false]
    · rw [decide_eq_false h2, Bool.false_and, Bool.and_false]

theorem flg_bit (p : ℕ → Bool) {e : ℕ} (he : e < 128) :
    (flg p >>> (7 * e + 6)) &&& 1 = if p e = true then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_shiftRight, tb_flg, tb1]
  by_cases hj : j < 1
  · obtain rfl : j = 0 := by omega
    rw [show (7 * e + 6 + 0) % 7 = 6 by omega, show (7 * e + 6 + 0) / 7 = e by omega,
      decide_eq_true (by omega : 7 * e + 6 + 0 < 7 * 128)]
    cases p e <;> rfl
  · rw [decide_eq_false hj, Bool.and_false]
    split
    · exact (small_tb (k := 1) (by norm_num) (by omega)).symm
    · simp

theorem flg_eq_zero {p : ℕ → Bool} (h : flg p = 0) : ∀ e < 128, p e = false := by
  intro e he
  have := flg_bit p he
  rw [h, Nat.zero_shiftRight, Nat.zero_and] at this
  cases hp : p e
  · rfl
  · rw [hp] at this
    exact absurd this (by decide)

theorem zl_eq (X : ℕ) : zl X = flg fun e => (X >>> (7 * e)) &&& 127 == 0 := by
  unfold zl HM LM
  rw [cen_strictN, lanesK_eq, lanesK_eq]
  simp only [nl_and, nl_or, nl_xor, Nat.add_eq]
  have hXL : X &&& lanes 7 (fun _ => 63) 128 = lanes 7 (fun e => (X >>> (7 * e)) &&& 63) 128 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, tb_lanes (f := fun _ => 63) (fun _ _ => by norm_num),
      tb_lanes (f := fun e => (X >>> (7 * e)) &&& 63)
        (fun _ _ => Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)),
      Nat.testBit_and, Nat.testBit_shiftRight, Nat.div_add_mod]
    cases X.testBit i <;> cases decide (i < 7 * 128) <;> simp
  rw [hXL, lanes_add]
  have hb : ∀ e < 128, ((X >>> (7 * e)) &&& 63) + 63 < 128 := fun e _ => by
    have := Nat.and_le_right (n := X >>> (7 * e)) (m := 63)
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, tb_lanes (f := fun _ => 64) (fun _ _ => by norm_num),
    tb_lanes (f := fun e => ((X >>> (7 * e)) &&& 63) + 63) hb, tb_flg]
  have hr : i % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hX : X.testBit i = ((X >>> (7 * (i / 7))) &&& 127).testBit (i % 7) := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, tb127, decide_eq_true hr, Bool.and_true,
      Nat.div_add_mod]
  have hS : (X >>> (7 * (i / 7))) &&& 63 = ((X >>> (7 * (i / 7))) &&& 127) &&& 63 := by
    rw [Nat.and_assoc]
    rfl
  have key : ∀ v < 128, ∀ r < 7, Bool.xor ((64 : ℕ).testBit r)
      ((64 : ℕ).testBit r && (((v &&& 63) + 63).testBit r || v.testBit r)) =
      (decide (r = 6) && (v == 0)) := by decide +kernel
  rw [hX, hS]
  have := key _ (ln_lt X (7 * (i / 7))) _ hr
  generalize (X >>> (7 * (i / 7))) &&& 127 = v at this ⊢
  generalize i % 7 = r at this ⊢
  cases decide (i < 7 * 128)
  · rfl
  · simpa using this

theorem lanes_pair (w : ℕ) (f : ℕ → ℕ) : ∀ n,
    lanes w f (2 * n) = lanes (2 * w) (fun k => f (2 * k) + 2 ^ w * f (2 * k + 1)) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    simp only [lanes]
    rw [lanes_pair w f n, show w * (2 * n + 1) = 2 * w * n + w by ring,
      show w * (2 * n) = 2 * w * n by ring, pow_add]
    ring

theorem sum_pairs (f : ℕ → ℕ) : ∀ n,
    ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) = ∑ e ∈ Finset.range (2 * n), f e
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_pairs f n, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem pop_lanes {b : ℕ → ℕ} (hb : ∀ e, b e ≤ 1) :
    ((lanes 7 b 128 % 16383) &&& 127) + ((lanes 7 b 128 % 16383) >>> 7) =
      ∑ e ∈ Finset.range 128, b e := by
  have h1 : lanes 7 b 128 = lanes 14 (fun k => b (2 * k) + 2 ^ 7 * b (2 * k + 1)) 64 := lanes_pair 7 b 64
  have h2 := lanes_mod (w := 14) (by norm_num) (fun k => b (2 * k) + 2 ^ 7 * b (2 * k + 1)) 64
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
  have hE : ∑ k ∈ Finset.range 64, b (2 * k) ≤ 64 := by
    calc ∑ k ∈ Finset.range 64, b (2 * k) ≤ ∑ _k ∈ Finset.range 64, 1 := Finset.sum_le_sum fun k _ => hb _
      _ = 64 := by simp
  have hO : ∑ k ∈ Finset.range 64, b (2 * k + 1) ≤ 64 := by
    calc ∑ k ∈ Finset.range 64, b (2 * k + 1) ≤ ∑ _k ∈ Finset.range 64, 1 :=
          Finset.sum_le_sum fun k _ => hb _
      _ = 64 := by simp
  have h4 : ∑ e ∈ Finset.range 128, b e =
      ∑ k ∈ Finset.range 64, b (2 * k) + ∑ k ∈ Finset.range 64, b (2 * k + 1) := by
    rw [← Finset.sum_add_distrib, sum_pairs]
  generalize ∑ k ∈ Finset.range 64, b (2 * k) = E at h2 hE h4
  generalize ∑ k ∈ Finset.range 64, b (2 * k + 1) = O at h2 hO h4
  have h3 : lanes 7 b 128 % 16383 = E + 128 * O := by
    rw [h1, show (16383 : ℕ) = 2 ^ 14 - 1 from rfl, h2]
    simp only [show (2 : ℕ) ^ 7 = 128 from rfl, show (2 : ℕ) ^ 14 - 1 = 16383 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h3, h4, Nat.and_two_pow_sub_one_eq_mod (E + 128 * O) 7, Nat.shiftRight_eq_div_pow]
  change (E + 128 * O) % 128 + (E + 128 * O) / 128 = E + O
  omega

theorem shr6_flg (p : ℕ → Bool) : flg p >>> 6 = lanes 7 (fun e => if p e = true then 1 else 0) 128 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, tb_flg,
    tb_lanes (f := fun e => if p e = true then 1 else 0) (fun e _ => by split <;> norm_num)]
  by_cases h : i % 7 = 0
  · rw [show (6 + i) % 7 = 6 by omega, show (6 + i) / 7 = i / 7 by omega, h]
    simp only [show (6 + i < 7 * 128 ↔ i < 7 * 128) from by omega]
    cases p (i / 7) <;> simp
  · rw [decide_eq_false (show ¬ (6 + i) % 7 = 6 by omega)]
    have : (if p (i / 7) = true then 1 else 0 : ℕ).testBit (i % 7) = false := by
      split
      · exact small_tb (k := 1) (by norm_num) (by omega)
      · simp
    rw [this]
    simp

theorem pop_eq (p : ℕ → Bool) : pop (flg p) = ∑ e ∈ Finset.range 128, if p e = true then 1 else 0 := by
  unfold pop
  rw [cen_strictN]
  simp only [nl_and, nl_shr, nl_mod, Nat.add_eq]
  rw [shr6_flg]
  exact pop_lanes fun e => by split <;> norm_num

theorem code_lo {e g : ℕ} (he : e < 128) : (e + 128 * g) &&& 127 = e := by
  rw [Nat.and_two_pow_sub_one_eq_mod (e + 128 * g) 7]
  change (e + 128 * g) % 128 = e
  omega

theorem code_hi {e g : ℕ} (he : e < 128) (hg : g < 512) : ((e + 128 * g) >>> 7) &&& 511 = g := by
  rw [Nat.and_two_pow_sub_one_eq_mod _ 9, Nat.shiftRight_eq_div_pow]
  change (e + 128 * g) / 128 % 512 = g
  omega

theorem code_split {q : ℕ} (hq : q < 65536) : q = (q &&& 127) + 128 * (q >>> 7) ∧ q &&& 127 < 128 ∧
    q >>> 7 < 512 := by
  rw [Nat.and_two_pow_sub_one_eq_mod q 7, Nat.shiftRight_eq_div_pow]
  change q = q % 128 + 128 * (q / 128) ∧ q % 128 < 128 ∧ q / 128 < 512
  omega

theorem sMulG_eq (AR MR : ℕ → ℕ) {e g e' h : ℕ} (he : e < 128) (hg : g < 512) (he' : e' < 128)
    (hh : h < 512) :
    sMulG AR MR (e + 128 * g) (e' + 128 * h) =
      (e ^^^ ((AR g >>> (7 * e')) &&& 127)) + 128 * ((MR g >>> (9 * h)) &&& 511) := by
  unfold sMulG
  simp only [cen_strictN]
  change ((e + 128 * g) &&& 127 ^^^ ((AR (((e + 128 * g) >>> 7) &&& 511) >>>
      (7 * ((e' + 128 * h) &&& 127))) &&& 127)) +
      128 * ((MR (((e + 128 * g) >>> 7) &&& 511) >>> (9 * (((e' + 128 * h) >>> 7) &&& 511))) &&& 511) = _
  rw [code_lo he, code_hi he hg, code_lo he', code_hi he' hh]

theorem code_eq {x y m m' : ℕ} (hx : x < 128) (hy : y < 128) :
    x + 128 * m = y + 128 * m' ↔ x = y ∧ m = m' := by
  omega

theorem xor_eq_zero {u v : ℕ} : u ^^^ v = 0 ↔ u = v := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases hu : u.testBit i <;> cases hv : v.testBit i <;> simp_all
  · rintro rfl
    exact Nat.xor_self u

theorem xor4 (x y z w : ℕ) : (x ^^^ w) ^^^ (z ^^^ y) = (x ^^^ y) ^^^ (z ^^^ w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases z.testBit i <;> cases w.testBit i <;> rfl

section Grp

variable (AR MR : ℕ → ℕ) {mul : ℕ → ℕ → ℕ}
  (hmul : ∀ c d, c < 65536 → d < 65536 → mul c d = sMulG AR MR c d)
include hmul

omit hmul in
theorem mt_lt (r h : ℕ) : (MR r >>> (9 * h)) &&& 511 < 512 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem mul_code {e g e' h : ℕ} (he : e < 128) (hg : g < 512) (he' : e' < 128) (hh : h < 512) :
    mul (e + 128 * g) (e' + 128 * h) =
      (e ^^^ ((AR g >>> (7 * e')) &&& 127)) + 128 * ((MR g >>> (9 * h)) &&& 511) := by
  rw [hmul _ _ (by omega) (by omega), sMulG_eq AR MR he hg he' hh]

omit hmul in
@[expose] def SqAt (g : ℕ) : Prop :=
  ∀ e < 128, (AR ((MR g >>> (9 * g)) &&& 511) >>> (7 * (e ^^^ ((AR g >>> (7 * e)) &&& 127)))) &&& 127 =
    ((AR ((MR g >>> (9 * g)) &&& 511) >>> (7 * e)) &&& 127) ^^^
      ((AR ((MR g >>> (9 * ((MR g >>> (9 * g)) &&& 511))) &&& 511) >>> (7 * e)) &&& 127)

theorem zS0_eq {g : ℕ} (hg : g < 512) :
    zS0 (AR g) ((MR g >>> (9 * g)) &&& 511) =
      flg fun e => decide (mul (e + 128 * g) (e + 128 * g) = 0) := by
  unfold zS0
  simp only [cen_nIf, cen_beq, decide_eq_true_eq, nl_xor]
  by_cases h2 : (MR g >>> (9 * g)) &&& 511 = 0
  · rw [if_pos h2, zl_eq]
    apply flg_congr
    intro e he
    rw [ln_xor, ln_IDX he, mul_code AR MR hmul he hg he hg, h2, Nat.mul_zero, Nat.add_zero,
      Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  · rw [if_neg h2]
    symm
    apply flg_false
    intro e he
    rw [mul_code AR MR hmul he hg he hg]
    simp only [decide_eq_false_iff_not]
    omega

theorem zI_eq {g : ℕ} (hg : g < 512) :
    zI g (flg fun e => decide (mul (e + 128 * g) (e + 128 * g) = 0)) =
      flg fun e => decide (mul (e + 128 * g) (e + 128 * g) = 0 ∧ e + 128 * g ≠ 0) := by
  unfold zI
  simp only [cen_nIf, cen_beq, decide_eq_true_eq, nl_xor, nl_and]
  by_cases g0 : g = 0
  · rw [if_pos g0, flg_64, flg_and, flg_xor]
    apply flg_congr
    intro e he
    subst g0
    simp only [Nat.mul_zero, Nat.add_zero]
    by_cases h1 : mul e e = 0 <;> by_cases h2 : e = 0 <;> simp [h1, h2]
  · rw [if_neg g0]
    apply flg_congr
    intro e he
    have : e + 128 * g ≠ 0 := by omega
    simp only [this, ne_eq, not_false_eq_true, and_true]

theorem zO_eq {g : ℕ} (hg : g < 512) (hsq : SqAt AR MR g) :
    zO AR MR (AR g) (MR g) ((MR g >>> (9 * g)) &&& 511)
        (flg fun e => decide (mul (e + 128 * g) (e + 128 * g) = 0)) =
      flg fun e => decide (mul (e + 128 * g) (e + 128 * g) ≠ 0 ∧
        mul (mul (e + 128 * g) (e + 128 * g)) (mul (e + 128 * g) (e + 128 * g)) = 0) := by
  have hg2 := mt_lt MR g g
  unfold zO
  simp only [cen_strictN, cen_nIf, cen_beq, decide_eq_true_eq, nl_xor, nl_and, nl_shr, Nat.mul_eq]
  by_cases h4 : (MR ((MR g >>> (9 * g)) &&& 511) >>> (9 * ((MR g >>> (9 * g)) &&& 511))) &&& 511 = 0
  · rw [if_pos h4, zl_eq, flg_and, flg_xor]
    apply flg_congr
    intro e he
    have hd := xor_lt he (ln_lt (AR g) (7 * e))
    simp only [ln_xor]
    rw [ln_IDX he, ← hsq e he, mul_code AR MR hmul he hg he hg, mul_code AR MR hmul hd hg2 hd hg2, h4]
    by_cases hL : (e ^^^ ((AR g >>> (7 * e)) &&& 127)) ^^^ ((AR ((MR g >>> (9 * g)) &&& 511) >>>
        (7 * (e ^^^ ((AR g >>> (7 * e)) &&& 127)))) &&& 127) = 0 <;>
      by_cases hS : (e ^^^ ((AR g >>> (7 * e)) &&& 127)) + 128 * ((MR g >>> (9 * g)) &&& 511) = 0 <;>
      simp [hL, hS]
  · rw [if_neg h4]
    symm
    apply flg_false
    intro e he
    have hd := xor_lt he (ln_lt (AR g) (7 * e))
    rw [mul_code AR MR hmul he hg he hg, mul_code AR MR hmul hd hg2 hd hg2]
    simp only [decide_eq_false_iff_not, not_and, not_not]
    intro _
    omega

theorem lowCnt_eq {g q : ℕ} (hg : g < 512) (hq : q < 65536) (p : ℕ → Bool) :
    lowCnt AR MR (AR g) (MR g) g (flg p) q =
      ∑ e ∈ Finset.range 128, if (p e && decide (mul (e + 128 * g) q = mul q (e + 128 * g))) = true
        then 1 else 0 := by
  obtain ⟨hqs, he', hh⟩ := code_split hq
  unfold lowCnt
  simp only [cen_strictN, cen_nIf, cen_beq, decide_eq_true_eq, nl_and, nl_shr, nl_xor, Nat.mul_eq]
  generalize q &&& 127 = e' at hqs he' ⊢
  generalize q >>> 7 = h at hqs hh ⊢
  subst hqs
  by_cases hm : (MR g >>> (9 * h)) &&& 511 = (MR h >>> (9 * g)) &&& 511
  · rw [if_pos hm, zl_eq, flg_and, pop_eq]
    refine Finset.sum_congr rfl fun e he => ?_
    have he := Finset.mem_range.1 he
    simp only [ln_xor]
    rw [ln_IDX he, ln_RU (xor_lt he' (ln_lt _ _)) he, mul_code AR MR hmul he hg he' hh,
      mul_code AR MR hmul he' hh he hg, hm, xor4]
    simp only [code_eq (xor_lt he (ln_lt _ _)) (xor_lt he' (ln_lt _ _))]
    by_cases hx : e ^^^ ((AR g >>> (7 * e')) &&& 127) = e' ^^^ ((AR h >>> (7 * e)) &&& 127) <;>
      simp [hx, xor_eq_zero]
  · rw [if_neg hm]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have he := Finset.mem_range.1 he
    rw [mul_code AR MR hmul he hg he' hh, mul_code AR MR hmul he' hh he hg]
    simp only [code_eq (xor_lt he (ln_lt _ _)) (xor_lt he' (ln_lt _ _))]
    simp [hm]

omit hmul in
theorem sum_ite_add (p : ℕ → Bool) (f1 f2 : ℕ → ℕ) (K : ℕ) :
    ∑ e ∈ Finset.range 128, (if p e = true then f1 e + f2 e * K else 0) =
      ∑ e ∈ Finset.range 128, (if p e = true then f1 e else 0) +
        (∑ e ∈ Finset.range 128, if p e = true then f2 e else 0) * K := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  split <;> simp

omit hmul in
theorem ite_and_one (a b : Bool) :
    (if (a && b) = true then 1 else 0 : ℕ) = if a = true then (if b = true then 1 else 0) else 0 := by
  cases a <;> cases b <;> rfl

theorem qWalk_eq {g : ℕ} (hg : g < 512) (p : ℕ → Bool) : ∀ Q : List ℕ,
    qWalk AR MR (AR g) (MR g) g (flg p) Q +
        ∑ e ∈ Finset.range 128, (if p e = true then cmU mul (e + 128 * g) Q else 0) =
      ∑ e ∈ Finset.range 128, (if p e = true then cmL mul (e + 128 * g) Q else 0)
  | [] => by
    have e1 : ∀ c, cmU mul c [] = 0 := fun _ => rfl
    have e2 : ∀ c, cmL mul c [] = 0 := fun _ => rfl
    change (0 : ℕ) + _ = _
    simp [e1, e2]
  | q :: Q => by
    have ih := qWalk_eq hg p Q
    have e1 : qWalk AR MR (AR g) (MR g) g (flg p) (q :: Q) =
        Nat.add (Bool.rec (motive := fun _ => ℕ) 0 (lowCnt AR MR (AR g) (MR g) g (flg p) q)
          (Nat.blt q 65536)) (Nat.shiftLeft (qWalk AR MR (AR g) (MR g) g (flg p) Q) 20) := rfl
    have e2 : ∀ c, cmU mul c (q :: Q) = Nat.add (Bool.rec (motive := fun _ => ℕ)
        (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (mul c q) (mul q c))) 0 (Nat.blt q 65536))
        (Nat.shiftLeft (cmU mul c Q) 20) := fun _ => rfl
    have e3 : ∀ c, cmL mul c (q :: Q) = Nat.add
        (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (mul c q) (mul q c)))
        (Nat.shiftLeft (cmL mul c Q) 20) := fun _ => rfl
    rw [e1]
    simp only [e2, e3, cen_nIf, cen_blt, cen_beq, cen_shl, Nat.add_eq, decide_eq_true_eq]
    rw [sum_ite_add, sum_ite_add, ← ih]
    by_cases hq : q < 65536
    · simp only [hq, ↓reduceIte]
      rw [lowCnt_eq AR MR hmul hg hq p]
      have h0 : ∑ e ∈ Finset.range 128, (if p e = true then (0 : ℕ) else 0) = 0 := by simp
      rw [h0]
      have h1 : ∑ e ∈ Finset.range 128,
          (if (p e && decide (mul (e + 128 * g) q = mul q (e + 128 * g))) = true then 1 else 0) =
          ∑ e ∈ Finset.range 128, (if p e = true then
            (if mul (e + 128 * g) q = mul q (e + 128 * g) then 1 else 0) else 0) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [ite_and_one]
        simp
      rw [h1]
      ring
    · simp only [hq, ↓reduceIte]
      ring

theorem uWalk_eq {g : ℕ} (hg : g < 512) (p : ℕ → Bool) : ∀ U : List ℕ, (∀ u ∈ U, u < 65536) →
    uWalk AR MR (AR g) (MR g) g (flg p) U =
      ∑ e ∈ Finset.range 128, (if p e = true then cmL mul (e + 128 * g) U else 0)
  | [], _ => by
    have e2 : ∀ c, cmL mul c [] = 0 := fun _ => rfl
    change (0 : ℕ) = _
    simp [e2]
  | u :: U, hU => by
    have ih := uWalk_eq hg p U fun v hv => hU v (List.mem_cons_of_mem u hv)
    have e1 : uWalk AR MR (AR g) (MR g) g (flg p) (u :: U) =
        Nat.add (lowCnt AR MR (AR g) (MR g) g (flg p) u)
          (Nat.shiftLeft (uWalk AR MR (AR g) (MR g) g (flg p) U) 20) := rfl
    have e3 : ∀ c, cmL mul c (u :: U) = Nat.add
        (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (mul c u) (mul u c)))
        (Nat.shiftLeft (cmL mul c U) 20) := fun _ => rfl
    rw [e1, lowCnt_eq AR MR hmul hg (hU u (List.mem_cons_self ..)) p, ih]
    simp only [e3, cen_nIf, cen_beq, cen_shl, Nat.add_eq, decide_eq_true_eq]
    rw [sum_ite_add]
    have h1 : (∑ e ∈ Finset.range 128,
        if (p e && decide (mul (e + 128 * g) u = mul u (e + 128 * g))) = true then 1 else 0) =
        ∑ e ∈ Finset.range 128, (if p e = true then
          (if mul (e + 128 * g) u = mul u (e + 128 * g) then 1 else 0) else 0) :=
      Finset.sum_congr rfl fun e _ => by
        rw [ite_and_one]
        simp
    rw [h1]

omit hmul in
theorem lsum_eq (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, lsum_eq f n, Finset.sum_range_succ]
    simp

omit hmul in
theorem cuSum_eq (g : ℕ) (p : ℕ → Bool) (Q : List ℕ) :
    cuSum mul g (flg p) Q = ∑ e ∈ Finset.range 128, (if p e = true then cmU mul (e + 128 * g) Q else 0) := by
  unfold cuSum
  rw [natRec_sum, lsum_eq]
  simp only [cen_nIf, cen_beq, decide_eq_true_eq, nl_and, nl_shr, Nat.add_eq, Nat.mul_eq]
  by_cases h0 : flg p = 0
  · rw [if_pos h0]
    symm
    apply Finset.sum_eq_zero
    intro e he
    rw [flg_eq_zero h0 e (Finset.mem_range.1 he)]
    rfl
  · rw [if_neg h0]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [flg_bit p (Finset.mem_range.1 he)]
    cases p e <;> simp

omit hmul in
theorem cen_split (Q U : List ℕ) (nQ c : ℕ) :
    cen mul Q U nQ c =
      (if mul c c = 0 ∧ c ≠ 0 then 1 + cmL mul c Q * 2 ^ 20 else 0) +
        (if mul c c ≠ 0 ∧ mul (mul c c) (mul c c) = 0 then cmL mul c U * 2 ^ (20 * (nQ + 1)) else 0) := by
  unfold cen
  rw [cen_strictN]
  simp only [cen_nIf, cen_beq, cen_shl, Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one, decide_eq_true_eq]
  by_cases hc : c = 0
  · subst hc
    by_cases h0 : mul 0 0 = 0 <;> by_cases h4 : mul (mul 0 0) (mul 0 0) = 0 <;> simp [h0, h4]
  · by_cases h0 : mul c c = 0 <;> by_cases h4 : mul (mul c c) (mul c c) = 0 <;> simp [h0, h4, hc] <;>
      ring

theorem grp_eq {g : ℕ} (hg : g < 512) (hsq : SqAt AR MR g) {Q U : List ℕ} (hU : ∀ u ∈ U, u < 65536)
    (nQ : ℕ) :
    grpG mul AR MR Q U nQ g = ∑ e ∈ Finset.range 128, cen mul Q U nQ (e + 128 * g) := by
  unfold grpG
  simp only [cen_strictN, nl_and, nl_shr, Nat.mul_eq]
  rw [zS0_eq AR MR hmul hg, zO_eq AR MR hmul hg hsq, zI_eq AR MR hmul hg]
  unfold grpT
  simp only [Nat.add_eq, cen_shl, Nat.mul_eq, Nat.succ_eq_add_one]
  have hq := qWalk_eq AR MR hmul hg
    (fun e => decide (mul (e + 128 * g) (e + 128 * g) = 0 ∧ e + 128 * g ≠ 0)) Q
  rw [pop_eq, cuSum_eq, uWalk_eq AR MR hmul hg _ U hU]
  simp only [cen_split, Finset.sum_add_distrib]
  have hA : ∑ e ∈ Finset.range 128, (if mul (e + 128 * g) (e + 128 * g) = 0 ∧ e + 128 * g ≠ 0 then
        1 + cmL mul (e + 128 * g) Q * 2 ^ 20 else 0) =
      ∑ e ∈ Finset.range 128, (if decide (mul (e + 128 * g) (e + 128 * g) = 0 ∧ e + 128 * g ≠ 0) = true
        then 1 else 0) +
      (∑ e ∈ Finset.range 128, (if decide (mul (e + 128 * g) (e + 128 * g) = 0 ∧ e + 128 * g ≠ 0) = true
        then cmL mul (e + 128 * g) Q else 0)) * 2 ^ 20 := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [decide_eq_true_eq]
    split_ifs <;> ring
  have hB : ∑ e ∈ Finset.range 128, (if mul (e + 128 * g) (e + 128 * g) ≠ 0 ∧
        mul (mul (e + 128 * g) (e + 128 * g)) (mul (e + 128 * g) (e + 128 * g)) = 0 then
        cmL mul (e + 128 * g) U * 2 ^ (20 * (nQ + 1)) else 0) =
      (∑ e ∈ Finset.range 128, (if decide (mul (e + 128 * g) (e + 128 * g) ≠ 0 ∧
        mul (mul (e + 128 * g) (e + 128 * g)) (mul (e + 128 * g) (e + 128 * g)) = 0) = true then
        cmL mul (e + 128 * g) U else 0)) * 2 ^ (20 * (nQ + 1)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [decide_eq_true_eq]
    split_ifs <;> ring
  rw [hA, hB, ← hq]
  ring

end Grp

theorem recAnd {P : ℕ → Bool} : ∀ {n : ℕ},
    Nat.rec (motive := fun _ => Bool) true (fun e ih => Bool.rec (motive := fun _ => Bool) false ih (P e)) n =
      true → ∀ e < n, P e = true
  | 0, _, e, he => absurd he (Nat.not_lt_zero _)
  | n + 1, h, e, he => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
        (fun e ih => Bool.rec (motive := fun _ => Bool) false ih (P e)) n) (P n) = true := h
    cases hp : P n
    · rw [hp] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hp] at h'
      rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
      · exact recAnd h' e he
      · exact hp

theorem sqAt_sound {AR MR : ℕ → ℕ} {g : ℕ} (h : sqAt AR MR g = true) : SqAt AR MR g := by
  unfold sqAt at h
  simp only [cen_strictB] at h
  intro e he
  have h2 := @recAnd (fun e => Nat.beq
    fld(AR fld(MR g, Nat.mul 9 g, 511), Nat.mul 7 (Nat.xor e fld(AR g, Nat.mul 7 e, 127)), 127)
    (Nat.xor fld(AR fld(MR g, Nat.mul 9 g, 511), Nat.mul 7 e, 127)
      fld(AR fld(MR g, Nat.mul 9 fld(MR g, Nat.mul 9 g, 511), 511), Nat.mul 7 e, 127))) 128 h e he
  have := Nat.eq_of_beq_eq_true h2
  simpa only [nl_and, nl_shr, nl_xor, Nat.mul_eq] using this

theorem sqFacts_of_blk {AR MR : ℕ → ℕ} (h : ∀ b < 8, sqBlk AR MR b = true) : ∀ g < 512, SqAt AR MR g := by
  intro g hg
  have h1 := h (g / 64) (by omega)
  unfold sqBlk at h1
  have hb := @recAnd (fun j => sqAt AR MR (Nat.add (Nat.mul 64 (g / 64)) j)) 64 h1 (g % 64)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (g / 64)) (g % 64) = g := by
    rw [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod g 64
  rw [e] at hb
  exact sqAt_sound hb

theorem blk_eq {AR MR : ℕ → ℕ} {mul : ℕ → ℕ → ℕ}
    (hmul : ∀ c d, c < 65536 → d < 65536 → mul c d = sMulG AR MR c d) (hsq : ∀ g < 512, SqAt AR MR g)
    {Q U : List ℕ} (hU : ∀ u ∈ U, u < 65536) (nQ : ℕ) {s : ℕ} (hs : s < 8) :
    blkG mul AR MR Q U nQ s = cenBlk mul Q U nQ (8192 * s) := by
  unfold blkG
  rw [natRec_sum, cenBlk, sumBelow_list _ (by norm_num : 8192 ≤ 64 * 128),
    show (8192 : ℕ) = 128 * 64 from rfl, sum_blocks _ 128 64]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj := List.mem_range.1 hj
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [grp_eq AR MR hmul (by omega) (hsq _ (by omega)) hU, lsum_eq]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  ring

end CFSG.KC.SBCenL

end
