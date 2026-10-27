module

public import Init
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.Fi22LH

@[expose] def lanes (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lanes w f n + 2 ^ (w * n) * f n

theorem lanes_zero (w : Nat) (f : Nat → Nat) : lanes w f 0 = 0 := rfl

theorem lanes_succ (w : Nat) (f : Nat → Nat) (n : Nat) :
    lanes w f (n + 1) = lanes w f n + 2 ^ (w * n) * f n := rfl

theorem lanes_lt {w : Nat} {f : Nat → Nat} : ∀ n, (∀ i < n, f i < 2 ^ w) → lanes w f n < 2 ^ (w * n)
  | 0, _ => by simp [lanes]
  | n + 1, hf => by
    have ih := lanes_lt n (fun i hi => hf i (by omega))
    have h1 := hf n (by omega)
    rw [lanes, Nat.mul_succ, Nat.pow_add]
    have : 2 ^ (w * n) * f n ≤ 2 ^ (w * n) * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : 2 ^ (w * n) * (2 ^ w - 1) + 2 ^ (w * n) = 2 ^ (w * n) * 2 ^ w := by
      have := Nat.one_le_two_pow (n := w)
      rw [Nat.mul_sub, Nat.mul_one]
      have := Nat.mul_le_mul_left (2 ^ (w * n)) this
      omega
    omega

theorem testBit_lanes {w : Nat} (hw : 0 < w) {f : Nat → Nat} : ∀ n, (∀ i < n, f i < 2 ^ w) →
    ∀ q, (lanes w f n).testBit q = (decide (q < w * n) && (f (q / w)).testBit (q % w))
  | 0, _, q => by simp [lanes]
  | n + 1, hf, q => by
    have hlt := lanes_lt n (fun i hi => hf i (by omega))
    rw [lanes, Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlt]
    split
    · next h =>
      rw [testBit_lanes hw n (fun i hi => hf i (by omega)) q, decide_eq_true h,
        decide_eq_true (show q < w * (n + 1) by rw [Nat.mul_succ]; omega)]
    · next h =>
      have hfn := hf n (by omega)
      by_cases h2 : q < w * (n + 1)
      · have e1 : q / w = n := by
          rw [Nat.div_eq_iff hw]
          constructor
          · rw [Nat.mul_comm]; omega
          · rw [Nat.mul_succ] at h2; rw [Nat.mul_comm]; omega
        have e2 : q % w = q - w * n := by
          have := Nat.div_add_mod q w
          rw [e1] at this
          omega
        rw [decide_eq_true h2, e1, e2, Bool.true_and]
      · rw [decide_eq_false h2, Bool.false_and]
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hfn
          (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_succ] at h2; omega))

theorem lanes_congr {w : Nat} {f g : Nat → Nat} : ∀ {n}, (∀ i < n, f i = g i) →
    lanes w f n = lanes w g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [lanes, lanes, lanes_congr fun i hi => h i (by omega), h n (by omega)]

theorem lanes_add (w : Nat) (f g : Nat → Nat) : ∀ n,
    lanes w f n + lanes w g n = lanes w (fun i => f i + g i) n
  | 0 => rfl
  | n + 1 => by
    simp only [lanes]
    rw [← lanes_add w f g n]
    ring

theorem lanes_sub {w : Nat} {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, g i ≤ f i) :
    lanes w f n - lanes w g n = lanes w (fun i => f i - g i) n := by
  have e := lanes_add w (fun i => f i - g i) g n
  rw [lanes_congr (g := f) (fun i hi => Nat.sub_add_cancel (h i hi))] at e
  omega

theorem lanes_mul_const (w : Nat) (f : Nat → Nat) (c : Nat) : ∀ n,
    c * lanes w f n = lanes w (fun i => c * f i) n
  | 0 => by simp [lanes]
  | n + 1 => by
    simp only [lanes]
    rw [← lanes_mul_const w f c n]
    ring

theorem lanes_cons (w : Nat) (f : Nat → Nat) : ∀ n,
    lanes w f (n + 1) = f 0 + 2 ^ w * lanes w (fun i => f (i + 1)) n
  | 0 => by simp [lanes]
  | n + 1 => by
    rw [lanes_succ, lanes_cons w f n, lanes_succ, show w * (n + 1) = w + w * n by ring,
      Nat.pow_add]
    ring

theorem lanes_shift {w : Nat} {f : Nat → Nat} (h0 : f 0 < 2 ^ w) (n : Nat) :
    lanes w f (n + 1) >>> w = lanes w (fun i => f (i + 1)) n := by
  rw [lanes_cons, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
    Nat.div_eq_of_lt h0, Nat.zero_add]

theorem lanes_top_zero {w : Nat} {f : Nat → Nat} {n : Nat} (h : f n = 0) :
    lanes w f (n + 1) = lanes w f n := by
  rw [lanes_succ, h, Nat.mul_zero, Nat.add_zero]

theorem lanes_regroup (u : Nat) (h : Nat → Nat) : ∀ n,
    lanes u h (2 * n) = lanes (2 * u) (fun j => h (2 * j) + 2 ^ u * h (2 * j + 1)) n
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, lanes_succ, lanes_succ, lanes_regroup u h n,
      lanes_succ]
    have e1 : 2 ^ (u * (2 * n)) = 2 ^ (2 * u * n) := by ring_nf
    have e2 : 2 ^ (u * (2 * n + 1)) = 2 ^ (2 * u * n) * 2 ^ u := by
      rw [← Nat.pow_add]
      ring_nf
    rw [e1, e2]
    ring

theorem lanes_mask {w t : Nat} (hw : 0 < w) (ht : t ≤ w) {f : Nat → Nat} {n : Nat}
    (hf : ∀ i < n, f i < 2 ^ w) :
    lanes w f n &&& lanes w (fun _ => 2 ^ t - 1) n = lanes w (fun i => f i % 2 ^ t) n := by
  have hm : ∀ i < n, 2 ^ t - 1 < 2 ^ w := fun _ _ =>
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos t) Nat.one_pos)
      (Nat.pow_le_pow_right (by decide) ht)
  have hr : ∀ i < n, f i % 2 ^ t < 2 ^ w := fun i _ =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos t)) (Nat.pow_le_pow_right (by decide) ht)
  apply Nat.eq_of_testBit_eq
  intro q
  rw [Nat.testBit_and, testBit_lanes hw n hf, testBit_lanes hw n hm, testBit_lanes hw n hr,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  cases decide (q < w * n) <;> cases (f (q / w)).testBit (q % w) <;> cases decide (q % w < t) <;>
    rfl

theorem lanes_bits {x : Nat} : ∀ {n}, x < 2 ^ n → x = lanes 1 (fun i => (x.testBit i).toNat) n := by
  intro n hx
  apply Nat.eq_of_testBit_eq
  intro q
  rw [testBit_lanes Nat.one_pos n (fun i _ => by cases x.testBit i <;> decide), Nat.div_one,
    Nat.mod_one, Nat.one_mul]
  by_cases hq : q < n
  · rw [decide_eq_true hq, Bool.true_and]
    cases x.testBit q <;> rfl
  · rw [decide_eq_false hq, Bool.false_and]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))

theorem lanes_ones_mul (w : Nat) : ∀ n, lanes w (fun _ => 1) n * (2 ^ w - 1) = 2 ^ (w * n) - 1
  | 0 => by simp [lanes]
  | n + 1 => by
    rw [lanes_succ, Nat.add_mul, lanes_ones_mul w n, Nat.mul_one, Nat.mul_succ, Nat.pow_add]
    have h1 := Nat.one_le_two_pow (n := w * n)
    have h2 := Nat.one_le_two_pow (n := w)
    rw [Nat.mul_sub, Nat.mul_one]
    have : 2 ^ (w * n) ≤ 2 ^ (w * n) * 2 ^ w := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos w)
    omega

theorem lanes_ones_eq {w : Nat} (hw : 0 < w) (n : Nat) :
    lanes w (fun _ => 1) n = (2 ^ (w * n) - 1) / (2 ^ w - 1) := by
  rw [← lanes_ones_mul w n, Nat.mul_div_cancel]
  have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 hw)
  omega

theorem pair_bits {x n : Nat} (hx : x < 2 ^ (2 * n)) :
    x - ((x >>> 1) &&& lanes 2 (fun _ => 1) n) =
      lanes 2 (fun j => (x.testBit (2 * j)).toNat + (x.testBit (2 * j + 1)).toNat) n := by
  have hb := lanes_bits hx
  have h2 : x = lanes 2 (fun j => (x.testBit (2 * j)).toNat + 2 * (x.testBit (2 * j + 1)).toNat) n := by
    conv_lhs => rw [hb]
    rw [lanes_regroup 1 _ n]
  have hm : (x >>> 1) &&& lanes 2 (fun _ => 1) n =
      lanes 2 (fun j => (x.testBit (2 * j + 1)).toNat) n := by
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lanes (by decide) n (fun _ _ => by decide),
      testBit_lanes (by decide) n (fun i _ => by cases x.testBit (2 * i + 1) <;> decide)]
    have hq := Nat.div_add_mod q 2
    rcases Nat.mod_two_eq_zero_or_one q with h | h
    · rw [h]
      have e : 1 + q = 2 * (q / 2) + 1 := by omega
      rw [e]
      cases decide (q < 2 * n) <;> cases x.testBit (2 * (q / 2) + 1) <;> rfl
    · rw [h]
      cases decide (q < 2 * n) <;> cases x.testBit (1 + q) <;> cases x.testBit (2 * (q / 2) + 1) <;>
        rfl
  have hs := lanes_sub (w := 2)
    (f := fun j => (x.testBit (2 * j)).toNat + 2 * (x.testBit (2 * j + 1)).toNat)
    (g := fun j => (x.testBit (2 * j + 1)).toNat) (n := n) fun i _ => by omega
  rw [← h2] at hs
  rw [hm, hs]
  apply lanes_congr
  intro i _
  omega

theorem pair_mask {w n : Nat} (hw : 0 < w) {g : Nat → Nat} (hg : ∀ i < 2 * n, g i < 2 ^ w) :
    (lanes w g (2 * n) &&& lanes (2 * w) (fun _ => 2 ^ w - 1) n) +
      ((lanes w g (2 * n) >>> w) &&& lanes (2 * w) (fun _ => 2 ^ w - 1) n) =
      lanes (2 * w) (fun j => g (2 * j) + g (2 * j + 1)) n := by
  have hpos : 0 < 2 * w := by omega
  have hl : ∀ (h : Nat → Nat), (∀ i < 2 * n, h i < 2 ^ w) →
      lanes w h (2 * n) &&& lanes (2 * w) (fun _ => 2 ^ w - 1) n =
        lanes (2 * w) (fun j => h (2 * j)) n := by
    intro h hh
    rw [lanes_regroup, lanes_mask hpos (by omega)]
    · apply lanes_congr
      intro j hj
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hh _ (by omega))]
    · intro j hj
      have h1 := hh (2 * j) (by omega)
      have h2 := hh (2 * j + 1) (by omega)
      have : 2 ^ w * h (2 * j + 1) ≤ 2 ^ w * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
      have e : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [← Nat.pow_add]; ring_nf
      rw [e]
      have : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * 2 ^ w := by
        rw [Nat.mul_sub, Nat.mul_one]
        have := Nat.le_mul_of_pos_right (2 ^ w) (Nat.two_pow_pos w)
        omega
      omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lanes]
  have hs : lanes w g (2 * n) >>> w =
      lanes w (fun i => if i + 1 < 2 * n then g (i + 1) else 0) (2 * n) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm, lanes_shift (hg 0 (by omega)), lanes_top_zero (by simp)]
    apply lanes_congr
    intro i hi
    rw [if_pos (by omega)]
  rw [hl g hg, hs, hl _ fun i hi => by split <;> [exact hg _ ‹_›; exact Nat.two_pow_pos w],
    lanes_add]
  apply lanes_congr
  intro j hj
  rw [if_pos (by omega)]

theorem pair_addShift {w n : Nat} (hw : 0 < w) {g : Nat → Nat}
    (hg : ∀ i < 2 * n, g i + (if i + 1 < 2 * n then g (i + 1) else 0) < 2 ^ w) :
    (lanes w g (2 * n) + (lanes w g (2 * n) >>> w)) &&& lanes (2 * w) (fun _ => 2 ^ w - 1) n =
      lanes (2 * w) (fun j => g (2 * j) + g (2 * j + 1)) n := by
  have hpos : 0 < 2 * w := by omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lanes]
  have hg0 : ∀ i < 2 * n, g i < 2 ^ w := fun i hi => Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (hg i hi)
  have hs : lanes w g (2 * n) >>> w =
      lanes w (fun i => if i + 1 < 2 * n then g (i + 1) else 0) (2 * n) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm, lanes_shift (hg0 0 (by omega)), lanes_top_zero (by simp)]
    apply lanes_congr
    intro i hi
    rw [if_pos (by omega)]
  rw [hs, lanes_add, lanes_regroup, lanes_mask hpos (by omega)]
  · apply lanes_congr
    intro j hj
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hg _ (by omega)), if_pos (by omega)]
  · intro j hj
    have h1 := hg (2 * j) (by omega)
    have h2 := hg (2 * j + 1) (by omega)
    have : 2 ^ w * (g (2 * j + 1) + if 2 * j + 1 + 1 < 2 * n then g (2 * j + 1 + 1) else 0) ≤
        2 ^ w * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by rw [← Nat.pow_add]; ring_nf
    rw [e]
    have : 2 ^ w * (2 ^ w - 1) + 2 ^ w = 2 ^ w * 2 ^ w := by
      rw [Nat.mul_sub, Nat.mul_one]
      have := Nat.le_mul_of_pos_right (2 ^ w) (Nat.two_pow_pos w)
      omega
    omega

theorem addShift_lt {w n : Nat} (hw : 0 < w) {g : Nat → Nat}
    (hg : ∀ i < 2 * n, g i + (if i + 1 < 2 * n then g (i + 1) else 0) < 2 ^ w) :
    lanes w g (2 * n) + (lanes w g (2 * n) >>> w) < 2 ^ (w * (2 * n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [lanes]
  have hg0 : ∀ i < 2 * n, g i < 2 ^ w := fun i hi => Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (hg i hi)
  have hs : lanes w g (2 * n) >>> w =
      lanes w (fun i => if i + 1 < 2 * n then g (i + 1) else 0) (2 * n) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 1 := ⟨2 * n - 1, by omega⟩
    rw [hm, lanes_shift (hg0 0 (by omega)), lanes_top_zero (by simp)]
    apply lanes_congr
    intro i hi
    rw [if_pos (by omega)]
  rw [hs, lanes_add]
  exact lanes_lt _ hg

@[expose] def psum (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, j => psum f m j + if m ≤ j then f (j - m) else 0

theorem psum_le {f : Nat → Nat} {B : Nat} (hf : ∀ i, f i ≤ B) : ∀ m j, psum f m j ≤ m * B
  | 0, _ => by simp [psum]
  | m + 1, j => by
    rw [psum, Nat.succ_mul]
    have := psum_le hf m j
    split
    · have := hf (j - m)
      omega
    · omega

theorem lanes_split (w : Nat) (g : Nat → Nat) (n : Nat) : ∀ k,
    lanes w g (n + k) = lanes w g n + 2 ^ (w * n) * lanes w (fun i => g (n + i)) k
  | 0 => by simp [lanes]
  | k + 1 => by
    rw [← Nat.add_assoc, lanes_succ, lanes_split w g n k, lanes_succ, Nat.mul_add, Nat.add_assoc,
      Nat.mul_add, Nat.pow_add]
    ring

theorem lanes_trunc {w : Nat} {g : Nat → Nat} {n : Nat} (hg : ∀ i < n, g i < 2 ^ w) (k : Nat) :
    lanes w g (n + k) % 2 ^ (w * n) = lanes w g n := by
  rw [lanes_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lanes_lt n hg)]

theorem lanes_mul_pow (w : Nat) (g : Nat → Nat) : ∀ m n,
    lanes w g n * 2 ^ (w * m) = lanes w (fun j => if m ≤ j then g (j - m) else 0) (n + m)
  | 0, n => by
    rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    apply lanes_congr
    intro i _
    simp
  | m + 1, n => by
    rw [Nat.mul_succ, Nat.pow_add, ← Nat.mul_assoc, lanes_mul_pow w g m n, ← Nat.add_assoc,
      lanes_cons]
    rw [if_neg (by omega), Nat.zero_add, Nat.mul_comm]
    apply congrArg
    apply lanes_congr
    intro i _
    by_cases h : m ≤ i
    · rw [if_pos h, if_pos (by omega)]
      congr 1
      omega
    · rw [if_neg h, if_neg (by omega)]

theorem lanes_mul_ones {w : Nat} {f : Nat → Nat} {n B : Nat} (hf : ∀ i, f i ≤ B)
    (hB : n * B < 2 ^ w) : ∀ m, m ≤ n →
      (lanes w f n * lanes w (fun _ => 1) m) % 2 ^ (w * n) = lanes w (psum f m) n
  | 0, _ => by
    rw [lanes_zero, Nat.mul_zero, Nat.zero_mod]
    symm
    have : ∀ k, lanes w (psum f 0) k = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [lanes_succ, ih]
        rfl
    exact this n
  | m + 1, hm => by
    have hlt : ∀ m' ≤ n, ∀ i < n, psum f m' i < 2 ^ w := fun m' hm' i _ =>
      Nat.lt_of_le_of_lt (Nat.le_trans (psum_le hf m' i) (Nat.mul_le_mul_right _ hm')) hB
    have hsh : (lanes w f n * 2 ^ (w * m)) % 2 ^ (w * n) =
        lanes w (fun j => if m ≤ j then f (j - m) else 0) n := by
      rw [lanes_mul_pow, lanes_trunc]
      intro i _
      split
      · exact Nat.lt_of_le_of_lt (Nat.le_trans (hf _) (Nat.le_mul_of_pos_left _ (by omega))) hB
      · exact Nat.two_pow_pos w
    rw [lanes_succ, Nat.mul_add, Nat.mul_one, Nat.add_mod, lanes_mul_ones hf hB m (by omega), hsh,
      lanes_add, Nat.mod_eq_of_lt]
    · rfl
    · exact lanes_lt n fun i hi => hlt (m + 1) hm i hi

end CFSG.KS.Fi22LH
