module

public import CFSG.Certificates.Kernel.AxisPlane.Sound
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.SuccPred
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

public section

set_option maxHeartbeats 400000

namespace CFSG.KC.AxisPlane

open CFSG.KC.Benes

@[expose] def lanes (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lanes w f n + 2 ^ (w * n) * f n

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
        exact Nat.lt_of_lt_of_le hfn (Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_succ] at h2; omega))

theorem lanes_add (w : Nat) (f g : Nat → Nat) : ∀ n,
    lanes w f n + lanes w g n = lanes w (fun i => f i + g i) n
  | 0 => rfl
  | n + 1 => by
    simp only [lanes]
    rw [← lanes_add w f g n]
    ring

@[expose] def cnt (x s i : Nat) : Nat :=
  ∑ j ∈ Finset.range (2 ^ s), (x.testBit (2 ^ s * i + j)).toNat

theorem cnt_le (x s i : Nat) : cnt x s i ≤ 2 ^ s := by
  unfold cnt
  calc ∑ j ∈ Finset.range (2 ^ s), (x.testBit (2 ^ s * i + j)).toNat
      ≤ ∑ _j ∈ Finset.range (2 ^ s), 1 := Finset.sum_le_sum fun j _ => toNat_le_one' _
    _ = 2 ^ s := by simp
where
  toNat_le_one' (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem cnt_lt (x s i : Nat) : cnt x s i < 2 ^ 2 ^ s :=
  Nat.lt_of_le_of_lt (cnt_le x s i) (Nat.pow_lt_pow_right (by decide) Nat.lt_two_pow_self)

theorem cnt_succ (x s i : Nat) : cnt x (s + 1) i = cnt x s (2 * i) + cnt x s (2 * i + 1) := by
  unfold cnt
  rw [Nat.pow_succ, Nat.mul_two, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    ring

theorem cnt_zero (x i : Nat) : cnt x 0 i = (x.testBit i).toNat := by
  simp [cnt]

theorem sum_cnt (x s : Nat) : ∀ n, ∑ i ∈ Finset.range n, cnt x s i =
    ∑ j ∈ Finset.range (2 ^ s * n), (x.testBit j).toNat
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_cnt x s n, Nat.mul_succ, Finset.sum_range_add]
    rfl

theorem popStep_lanes {s n : Nat} (hn : 2 ^ s * (2 * n) = 16777216) (x : Nat) :
    popStep s (lanes (2 ^ s) (cnt x s) (2 * n)) = lanes (2 ^ (s + 1)) (cnt x (s + 1)) n := by
  have hw : 0 < 2 ^ s := Nat.two_pow_pos s
  have hM : ∀ q, (popM s).testBit q = (decide (q < 2 ^ (s + 1) * n) && decide (q % 2 ^ (s + 1) < 2 ^ s)) := by
    intro q
    have hW : wW = 2 ^ (s + 1) * n := by
      rw [show 2 ^ (s + 1) * n = 2 ^ s * (2 * n) by ring, hn]
      rfl
    have hc : 2 ^ 2 ^ s - 1 < 2 ^ 2 ^ (s + 1) :=
      Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
        (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
    have := testBit_mul_div (Nat.two_pow_pos (s + 1)) hW hc q
    have e1 : popM s = (2 ^ 2 ^ s - 1) * ((2 ^ wW - 1) / (2 ^ 2 ^ (s + 1) - 1)) := by
      unfold popM repW onesW
      simp only [nmul, nshl, nsub, ndiv, nadd, Nat.one_shiftLeft]
    rw [e1, this, Nat.testBit_two_pow_sub_one, show wW = 2 ^ (s + 1) * n from hW]
  have hf : ∀ i < 2 * n, cnt x s i < 2 ^ 2 ^ s := fun i _ => cnt_lt x s i
  have hg : ∀ i < n, cnt x s (2 * i) < 2 ^ 2 ^ (s + 1) := fun i _ =>
    Nat.lt_of_lt_of_le (cnt_lt x s _) (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hg' : ∀ i < n, cnt x s (2 * i + 1) < 2 ^ 2 ^ (s + 1) := fun i _ =>
    Nat.lt_of_lt_of_le (cnt_lt x s _) (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) (by omega)))
  have h2w : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ, Nat.mul_comm]
  have hcb : ∀ i, cnt x s i < 2 ^ 2 ^ s := cnt_lt x s
  have hA : Nat.land (lanes (2 ^ s) (cnt x s) (2 * n)) (popM s) =
      lanes (2 ^ (s + 1)) (fun i => cnt x s (2 * i)) n := by
    apply Nat.eq_of_testBit_eq
    intro q
    rw [nland, Nat.testBit_and, testBit_lanes hw _ hf, hM, testBit_lanes (Nat.two_pow_pos _) _ hg,
      h2w]
    generalize cnt x s = f at hcb ⊢
    generalize 2 ^ s = w at hw hcb ⊢
    have hk := Nat.div_add_mod q (2 * w)
    generalize q / (2 * w) = k at hk
    have hr : q % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
    generalize q % (2 * w) = r at hk hr
    subst hk
    have e0 : w * (2 * n) = 2 * w * n := by ring
    rw [e0]
    by_cases hrw : r < w
    · have e1 : (2 * w * k + r) / w = 2 * k := by
        rw [show 2 * w * k + r = r + w * (2 * k) by ring, Nat.add_mul_div_left _ _ hw,
          Nat.div_eq_of_lt hrw, Nat.zero_add]
      have e2 : (2 * w * k + r) % w = r := by
        rw [show 2 * w * k + r = r + w * (2 * k) by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hrw]
      rw [e1, e2, decide_eq_true hrw]
      cases decide (2 * w * k + r < 2 * w * n) <;> simp
    · have hz : (f (2 * k)).testBit r = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hcb _) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hrw, hz]
  have hB : Nat.land (Nat.shiftRight (lanes (2 ^ s) (cnt x s) (2 * n)) (Nat.shiftLeft 1 s)) (popM s) =
      lanes (2 ^ (s + 1)) (fun i => cnt x s (2 * i + 1)) n := by
    apply Nat.eq_of_testBit_eq
    intro q
    rw [nland, nshr, nshl, Nat.one_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
      testBit_lanes hw _ hf, hM, testBit_lanes (Nat.two_pow_pos _) _ hg', h2w]
    generalize cnt x s = f at hcb ⊢
    generalize 2 ^ s = w at hw hcb ⊢
    have hk := Nat.div_add_mod q (2 * w)
    generalize q / (2 * w) = k at hk
    have hr : q % (2 * w) < 2 * w := Nat.mod_lt _ (by omega)
    generalize q % (2 * w) = r at hk hr
    subst hk
    have e0 : w * (2 * n) = 2 * w * n := by ring
    rw [e0]
    by_cases hrw : r < w
    · have e1 : (w + (2 * w * k + r)) / w = 2 * k + 1 := by
        rw [show w + (2 * w * k + r) = r + w * (2 * k + 1) by ring, Nat.add_mul_div_left _ _ hw,
          Nat.div_eq_of_lt hrw, Nat.zero_add]
      have e2 : (w + (2 * w * k + r)) % w = r := by
        rw [show w + (2 * w * k + r) = r + w * (2 * k + 1) by ring, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hrw]
      have hiff : (w + (2 * w * k + r) < 2 * w * n) ↔ (2 * w * k + r < 2 * w * n) := by
        constructor
        · intro h
          omega
        · intro h
          have hkn : k < n := by
            by_contra hc
            have : 2 * w * n ≤ 2 * w * k := Nat.mul_le_mul_left _ (by omega)
            omega
          have h3 : 2 * w * (k + 1) ≤ 2 * w * n := Nat.mul_le_mul_left _ hkn
          rw [Nat.mul_succ] at h3
          omega
      rw [e1, e2, decide_eq_true hrw, decide_eq_decide.2 hiff]
      cases decide (2 * w * k + r < 2 * w * n) <;> simp
    · have hz : (f (2 * k + 1)).testBit r = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hcb _) (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hrw, hz]
  unfold popStep
  rw [hA, hB, nadd, lanes_add]
  congr 1
  funext i
  rw [cnt_succ]

theorem lanes_zero (x : Nat) : Nat.land x onesW = lanes 1 (cnt x 0) 16777216 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [nland, Nat.testBit_and, testBit_onesW, testBit_lanes Nat.one_pos _ (fun i _ => cnt_lt x 0 i)]
  rw [Nat.div_one, Nat.mod_one, cnt_zero, Nat.one_mul]
  cases x.testBit q <;> simp [Bool.and_comm]

theorem lanes_mod {w : Nat} (hw : 0 < w) (f : Nat → Nat) : ∀ n,
    lanes w f n % (2 ^ w - 1) = (∑ i ∈ Finset.range n, f i) % (2 ^ w - 1)
  | 0 => by simp [lanes]
  | n + 1 => by
    have h1 : 2 ^ (w * n) % (2 ^ w - 1) = 1 % (2 ^ w - 1) := by
      have : 2 ^ w ≡ 1 [MOD 2 ^ w - 1] := by
        have := Nat.one_le_two_pow (n := w)
        exact (Nat.modEq_iff_dvd' this).2 (dvd_refl _) |>.symm
      have := this.pow n
      rw [one_pow, ← Nat.pow_mul] at this
      exact this
    rw [lanes, Finset.sum_range_succ, Nat.add_mod, lanes_mod hw f n, Nat.mul_mod, h1,
      ← Nat.mul_mod, Nat.one_mul, ← Nat.add_mod]

theorem popRec_lanes (x : Nat) : ∀ s, s ≤ 5 →
    Nat.rec (motive := fun _ => Nat) (Nat.land x onesW) (fun s ih => popStep s ih) s =
      lanes (2 ^ s) (cnt x s) (2 ^ (24 - s))
  | 0, _ => by rw [lanes_zero]; rfl
  | s + 1, hs => by
    change popStep s (Nat.rec (motive := fun _ => Nat) (Nat.land x onesW)
      (fun s ih => popStep s ih) s) = _
    rw [popRec_lanes x s (by omega)]
    have e : 2 ^ (24 - s) = 2 * 2 ^ (24 - (s + 1)) := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    rw [e]
    refine popStep_lanes ?_ x
    rw [← e, ← Nat.pow_add, show s + (24 - s) = 24 by omega]

theorem popK_eq (x : Nat) :
    popK x = ((Finset.range 16777216).filter fun q => x.testBit q = true).card := by
  have h5 : popK x = lanes (2 ^ 5) (cnt x 5) (2 ^ (24 - 5)) % (2 ^ 2 ^ 5 - 1) := by
    unfold popK
    exact congrArg (fun y => Nat.mod y 4294967295) (popRec_lanes x 5 (by omega))
  have h := lanes_mod (w := 2 ^ 5) (Nat.two_pow_pos 5) (cnt x 5) (2 ^ (24 - 5))
  rw [h5, h, sum_cnt]
  have hc : ∑ j ∈ Finset.range (2 ^ 5 * 2 ^ (24 - 5)), (x.testBit j).toNat =
      ((Finset.range 16777216).filter fun q => x.testBit q = true).card := by
    rw [show 2 ^ 5 * 2 ^ (24 - 5) = 16777216 by rfl, Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases x.testBit j <;> rfl
  rw [hc]
  apply Nat.mod_eq_of_lt
  calc _ ≤ (Finset.range 16777216).card := Finset.card_filter_le _ _
    _ < 2 ^ 2 ^ 5 - 1 := by simp

end CFSG.KC.AxisPlane

end
