module

public import Certificates.Data.Kernel.Misc.Hyp
public import Init.Data.Nat.Power2.Basic
import all Init.Data.Nat.Power2.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.KC.Ord

private theorem hypBits_letN_eq (y : Nat) (k : Nat → Nat) : letN y k = k y := by
  cases y <;> rfl

private def pbsum (W : Nat) (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pbsum W c n + c n * 2 ^ (W * n)

private theorem pbsum_lt {W : Nat} {c : Nat → Nat} (hc : ∀ b, c b < 2 ^ W) : ∀ n,
    pbsum W c n < 2 ^ (W * n)
  | 0 => by simp [pbsum]
  | n + 1 => by
    have h1 := pbsum_lt hc n
    have h2 : c n * 2 ^ (W * n) ≤ (2 ^ W - 1) * 2 ^ (W * n) :=
      Nat.mul_le_mul_right _ (by have := hc n; omega)
    have hW : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have e : 2 ^ (W * (n + 1)) = (2 ^ W - 1) * 2 ^ (W * n) + 2 ^ (W * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (2 ^ (W * n))]
      have : 2 ^ (W * n) ≤ 2 ^ W * 2 ^ (W * n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [pbsum, e]
    omega

private theorem testBit_pbsum {W : Nat} (hW : 0 < W) {c : Nat → Nat}
    (hc : ∀ b, c b < 2 ^ W) (p : Nat) : ∀ n,
    (pbsum W c n).testBit p = (decide (p < W * n) && (c (p / W)).testBit (p % W))
  | 0 => by simp [pbsum]
  | n + 1 => by
    rw [pbsum, Nat.add_comm, Nat.mul_comm (c n),
      Nat.testBit_two_pow_mul_add _ (pbsum_lt hc n)]
    by_cases h : p < W * n
    · simp only [h, ↓reduceIte]
      rw [testBit_pbsum hW hc p n]
      have h' : p < W * (n + 1) := by rw [Nat.mul_succ]; omega
      simp [h, h']
    · simp only [h, ↓reduceIte]
      by_cases h2 : p < W * (n + 1)
      · have e1 : p / W = n := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega)
          (by rw [Nat.succ_mul, Nat.mul_comm]; rw [Nat.mul_succ] at h2; omega)
        have e2 : p % W = p - W * n := by
          have := Nat.div_add_mod p W
          rw [e1] at this
          omega
        simp [h2, e1, e2]
      · have h3 : (c n).testBit (p - W * n) = false := by
          refine Nat.testBit_lt_two_pow (lt_of_lt_of_le (hc n) ?_)
          exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ] at h2; omega)
        simp [h2, h3]

private theorem pbsum_add (W : Nat) (a b : Nat → Nat) : ∀ n,
    pbsum W a n + pbsum W b n = pbsum W (fun i => a i + b i) n
  | 0 => rfl
  | n + 1 => by
    rw [pbsum, pbsum, pbsum, ← pbsum_add W a b n]
    ring

private theorem pbsum_and {W n : Nat} (hW : 0 < W) {c : Nat → Nat} (hc : ∀ b, c b < 2 ^ W)
    {M : Nat} (hM : ∀ p, M.testBit p = (decide (p < 2 * W * n) && decide (p % (2 * W) < W))) :
    pbsum W c (2 * n) &&& M = pbsum (2 * W) (fun B => c (2 * B)) n := by
  have hc2 : ∀ B, c (2 * B) < 2 ^ (2 * W) :=
    fun B => lt_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_pbsum hW hc, hM, testBit_pbsum (by omega) hc2]
  have e : W * (2 * n) = 2 * W * n := by ring
  rw [e]
  have hp : p = p % (2 * W) + W * (2 * (p / (2 * W))) := by
    have := Nat.div_add_mod p (2 * W)
    calc p = 2 * W * (p / (2 * W)) + p % (2 * W) := this.symm
      _ = p % (2 * W) + W * (2 * (p / (2 * W))) := by ring
  have hr2 : p % (2 * W) < 2 * W := Nat.mod_lt _ (by omega)
  by_cases hr : p % (2 * W) < W
  · have e1 : p / W = 2 * (p / (2 * W)) := by
      conv_lhs => rw [hp]
      rw [Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
    have e2 : p % W = p % (2 * W) := by
      conv_lhs => rw [hp]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    rw [e1, e2]
    by_cases hpn : p < 2 * W * n <;> simp [hr, hpn]
  · have h3 : (c (2 * (p / (2 * W)))).testBit (p % (2 * W)) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hc _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hr, h3]

private theorem pbsum_shr_and {W n : Nat} (hW : 0 < W) {c : Nat → Nat} (hc : ∀ b, c b < 2 ^ W)
    {M : Nat} (hM : ∀ p, M.testBit p = (decide (p < 2 * W * n) && decide (p % (2 * W) < W))) :
    (pbsum W c (2 * n) >>> W) &&& M = pbsum (2 * W) (fun B => c (2 * B + 1)) n := by
  have hc2 : ∀ B, c (2 * B + 1) < 2 ^ (2 * W) :=
    fun B => lt_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pbsum hW hc, hM,
    testBit_pbsum (by omega) hc2]
  have e : W * (2 * n) = 2 * W * n := by ring
  rw [e]
  have hp : p = p % (2 * W) + W * (2 * (p / (2 * W))) := by
    have := Nat.div_add_mod p (2 * W)
    calc p = 2 * W * (p / (2 * W)) + p % (2 * W) := this.symm
      _ = p % (2 * W) + W * (2 * (p / (2 * W))) := by ring
  have hr2 : p % (2 * W) < 2 * W := Nat.mod_lt _ (by omega)
  by_cases hr : p % (2 * W) < W
  · have hp' : W + p = p % (2 * W) + W * (2 * (p / (2 * W)) + 1) := by
      conv_lhs => rw [hp]
      ring
    have e1 : (W + p) / W = 2 * (p / (2 * W)) + 1 := by
      rw [hp', Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hr, Nat.zero_add]
    have e2 : (W + p) % W = p % (2 * W) := by
      rw [hp', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    rw [e1, e2]
    by_cases hpn : p < 2 * W * n
    · have hq : p / (2 * W) < n := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc p < 2 * W * n := hpn
          _ = n * (2 * W) := by ring
      have hlt : W + p < 2 * W * n := by
        have h4 : W * (2 * (p / (2 * W)) + 1) + W ≤ 2 * W * n := by
          have : p / (2 * W) + 1 ≤ n := hq
          calc W * (2 * (p / (2 * W)) + 1) + W = 2 * W * (p / (2 * W) + 1) := by ring
            _ ≤ 2 * W * n := Nat.mul_le_mul_left _ this
        omega
      simp [hr, hpn, hlt]
    · simp [hpn]
  · have h3 : (c (2 * (p / (2 * W)) + 1)).testBit (p % (2 * W)) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hc _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hr, h3]

private def pcnt (x : Nat) : Nat → Nat → Nat
  | 0, b => (x.testBit b).toNat
  | k + 1, b => pcnt x k (2 * b) + pcnt x k (2 * b + 1)

private theorem pcnt_eq (x : Nat) : ∀ k b,
    pcnt x k b = ((List.range (2 ^ k)).filter fun j => x.testBit (b * 2 ^ k + j)).length
  | 0, b => by
    simp only [pcnt, Nat.pow_zero, Nat.mul_one, List.range_one, List.filter_cons, List.filter_nil,
      Nat.add_zero]
    cases x.testBit b <;> rfl
  | k + 1, b => by
    rw [pcnt, pcnt_eq x k, pcnt_eq x k, Nat.pow_succ, Nat.mul_two, List.range_add,
      List.filter_append, List.length_append, List.filter_map, List.length_map]
    congr 2
    · apply List.filter_congr
      intro j _
      congr 1
      ring
    · apply List.filter_congr
      intro j _
      simp only [Function.comp]
      congr 1
      ring

private theorem pcnt_le (x k b : Nat) : pcnt x k b ≤ 2 ^ k := by
  rw [pcnt_eq]
  exact (List.length_filter_le _ _).trans (by simp)

private theorem pcnt_lt (x k b : Nat) : pcnt x k b < 2 ^ 2 ^ k :=
  lt_of_le_of_lt (pcnt_le x k b) (Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self)

private def pgeom (L : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pgeom L n + 2 ^ (L * n)

private theorem pgeom_mul (L : Nat) : ∀ n, (2 ^ L - 1) * pgeom L n = 2 ^ (L * n) - 1
  | 0 => by simp [pgeom]
  | n + 1 => by
    rw [pgeom, Nat.mul_add, pgeom_mul L n, Nat.mul_succ, Nat.pow_add]
    have h1 : 1 ≤ 2 ^ (L * n) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ L = a + 1 := ⟨2 ^ L - 1, by omega⟩
    rw [ha, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, Nat.mul_comm a]
    omega

private theorem pgeom_div {L : Nat} (hL : 0 < L) (n : Nat) :
    (2 ^ (L * n) - 1) / (2 ^ L - 1) = pgeom L n := by
  have h : 0 < 2 ^ L - 1 := by
    have := Nat.one_lt_two_pow (n := L) (by omega)
    omega
  rw [← pgeom_mul L n, Nat.mul_div_cancel_left _ h]

private theorem testBit_pgeom_mul {L c : Nat} (hc : c < 2 ^ L) : ∀ n q,
    (c * pgeom L n).testBit q = (decide (q < L * n) && c.testBit (q % L))
  | 0, q => by simp [pgeom]
  | n + 1, q => by
    have hlt : c * pgeom L n < 2 ^ (L * n) := by
      have h1 : c * pgeom L n ≤ (2 ^ L - 1) * pgeom L n := Nat.mul_le_mul_right _ (by omega)
      rw [pgeom_mul L n] at h1
      have := Nat.one_le_two_pow (n := L * n)
      omega
    rw [pgeom, Nat.mul_add, Nat.add_comm, Nat.mul_comm c (2 ^ _),
      Nat.testBit_two_pow_mul_add _ hlt, Nat.mul_succ]
    split
    · next h => rw [testBit_pgeom_mul hc n q, decide_eq_true h, decide_eq_true (by omega)]
    · next h =>
      by_cases h2 : q < L * n + L
      · rw [decide_eq_true h2, Bool.true_and]
        have : q % L = q - L * n := by
          rw [← Nat.sub_mul_mod (x := q) (k := n) (n := L) (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [this]
      · rw [decide_eq_false h2, Bool.false_and]
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega))

private theorem testBit_mul_div {W L n c : Nat} (hL : 0 < L) (hW : W = L * n)
    (hc : c < 2 ^ L) (q : Nat) :
    (c * ((2 ^ W - 1) / (2 ^ L - 1))).testBit q = (decide (q < W) && c.testBit (q % L)) := by
  rw [hW, pgeom_div hL, testBit_pgeom_mul hc]

private theorem hypBits_mask_eq (w : Nat) :
    pop1024.mask w = (2 ^ w - 1) * ((2 ^ 1024 - 1) / (2 ^ (2 * w) - 1)) := by
  simp only [pop1024.mask]
  change (1 <<< 1024 - 1) / (1 <<< (2 * w) - 1) * (1 <<< w - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, Nat.one_mul]
  exact Nat.mul_comm _ _

private theorem testBit_mask (w q : Nat) (hw : 0 < w)
    (hW : 1024 = 2 * w * (1024 / (2 * w))) :
    (pop1024.mask w).testBit q = (decide (q < 1024) && decide (q % (2 * w) < w)) := by
  have hc : 2 ^ w - 1 < 2 ^ (2 * w) := by
    have h1 : w < 2 * w := by omega
    have h2 : 2 ^ w < 2 ^ (2 * w) := Nat.pow_lt_pow_right (by norm_num) h1
    have h3 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    omega
  rw [hypBits_mask_eq]
  rw [testBit_mul_div (W := 1024) (L := 2 * w) (n := 1024 / (2 * w)) (c := 2 ^ w - 1)
    (by omega) hW hc q, Nat.testBit_two_pow_sub_one]

private theorem two_pow_mul_div_1024 (m : Nat) (hm : m ≤ 9) :
    2 * 2 ^ m * (1024 / (2 * 2 ^ m)) = 1024 := by
  have h : 2 * 2 ^ m = 2 ^ (m + 1) := by rw [Nat.pow_succ']
  rw [h]
  have hdvd : 2 ^ (m + 1) ∣ 1024 := by
    refine ⟨2 ^ (9 - m), ?_⟩
    rw [show (1024 : Nat) = 2 ^ 10 from by norm_num, ← Nat.pow_add]
    congr 1
    omega
  rw [Nat.mul_comm, Nat.div_mul_cancel hdvd]

private theorem half_1024 (m : Nat) (hm : m ≤ 9) :
    1024 / 2 ^ m = 2 * (1024 / (2 * 2 ^ m)) := by
  have h1 : 1024 / 2 ^ m = 2 ^ (10 - m) := by
    rw [show (1024 : Nat) = 2 ^ 10 from by norm_num, Nat.pow_div (by omega) (by norm_num)]
  have h2 : 1024 / (2 * 2 ^ m) = 2 ^ (9 - m) := by
    have h : 2 * 2 ^ m = 2 ^ (m + 1) := by rw [Nat.pow_succ']
    rw [show (1024 : Nat) = 2 ^ 10 from by norm_num, h,
      Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  rw [h1, h2, ← Nat.pow_succ']
  congr 1
  omega

private noncomputable def popStep (i acc : Nat) : Nat :=
  letN acc fun acc => letN (Nat.pow 2 i) fun w => letN (pop1024.mask w) fun m =>
    Nat.add (Nat.land acc m) (Nat.land (Nat.shiftRight acc w) m)

private theorem popStep_eq (i acc : Nat) :
    popStep i acc =
      (acc &&& pop1024.mask (2 ^ i)) + ((acc >>> 2 ^ i) &&& pop1024.mask (2 ^ i)) := by
  simp only [popStep, hypBits_letN_eq]
  rfl

private theorem pop1024_aux (C : Nat) (hC : C < 2 ^ 1024) :
    ∀ i ≤ 10, Nat.rec C popStep i = pbsum (2 ^ i) (pcnt C i) (1024 / 2 ^ i) := by
  intro i
  induction i with
  | zero =>
    intro _
    apply Nat.eq_of_testBit_eq
    intro p
    change C.testBit p = (pbsum 1 (pcnt C 0) 1024).testBit p
    rw [testBit_pbsum (W := 1) (by norm_num) (c := pcnt C 0) (fun b => by
      simpa using pcnt_lt C 0 b)]
    simp only [Nat.one_mul, Nat.div_one, Nat.mod_one, pcnt]
    by_cases hp : p < 1024
    · cases C.testBit p <;> simp [hp]
    · have hlt : C.testBit p = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hC (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hp, hlt]
  | succ m ih =>
    intro hm
    have hm' : m ≤ 10 := by omega
    have hm9 : m ≤ 9 := by omega
    rw [show Nat.rec C popStep (m + 1) = popStep m (Nat.rec C popStep m) from rfl,
      ih hm', popStep_eq]
    have hW := (two_pow_mul_div_1024 m hm9).symm
    have hM : ∀ p, (pop1024.mask (2 ^ m)).testBit p =
        (decide (p < 2 * 2 ^ m * (1024 / (2 * 2 ^ m))) && decide (p % (2 * 2 ^ m) < 2 ^ m)) := by
      intro p
      rw [testBit_mask (2 ^ m) p (by positivity) hW, ← hW]
    rw [half_1024 m hm9, pbsum_and (by positivity) (pcnt_lt C m) hM,
      pbsum_shr_and (by positivity) (pcnt_lt C m) hM, pbsum_add, ← Nat.pow_succ']
    rfl

theorem pop1024_eq {C : Nat} (hC : C < 2 ^ 1024) :
    pop1024 C = ((List.range 1024).filter fun j => C.testBit j).length := by
  have h := pop1024_aux C hC 10 le_rfl
  have hpop : pop1024 C = Nat.rec C popStep 10 := rfl
  rw [hpop, h]
  have e : (1024 : Nat) / 2 ^ 10 = 1 := by norm_num
  rw [e, pbsum, pbsum, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, pcnt_eq]
  simp

private noncomputable def bitStep (C : Nat) (b pos : Nat) : Nat :=
  letN pos fun pos => letN (pos + 2 ^ (9 - b)) fun q =>
    Bool.rec (motive := fun _ => Nat) pos q (notB (Nat.beq (C >>> q) 0))

private theorem pow_shiftRight_ne_zero (j q : Nat) : (2 ^ j >>> q) ≠ 0 ↔ q ≤ j := by
  rw [Nat.shiftRight_eq_div_pow, ← Nat.pos_iff_ne_zero, Nat.div_pos_iff]
  rw [Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)]
  simp

private theorem bitStep_arith (j b : Nat) (hb : b ≤ 9) :
    (if j - j % 2 ^ (10 - b) + 2 ^ (9 - b) ≤ j
      then j - j % 2 ^ (10 - b) + 2 ^ (9 - b)
      else j - j % 2 ^ (10 - b)) = j - j % 2 ^ (9 - b) := by
  have hA2 : 2 ^ (10 - b) = 2 * 2 ^ (9 - b) := by
    rw [show 10 - b = (9 - b) + 1 by omega, Nat.pow_succ']
  have htpos : 0 < 2 ^ (9 - b) := by positivity
  have hrlt : j % 2 ^ (10 - b) < 2 ^ (10 - b) := Nat.mod_lt _ (by positivity)
  have hP : j - j % 2 ^ (10 - b) = 2 ^ (10 - b) * (j / 2 ^ (10 - b)) := by
    have h := Nat.div_add_mod j (2 ^ (10 - b))
    omega
  have hQj : (j - j % 2 ^ (10 - b) + 2 ^ (9 - b) ≤ j) ↔
      2 ^ (9 - b) ≤ j % 2 ^ (10 - b) := by
    have h := Nat.div_add_mod j (2 ^ (10 - b))
    constructor <;> intro hh <;> omega
  have hjt : j / 2 ^ (9 - b) =
      2 * (j / 2 ^ (10 - b)) + j % 2 ^ (10 - b) / 2 ^ (9 - b) := by
    have hdec : j = j % 2 ^ (10 - b) + 2 ^ (9 - b) * (2 * (j / 2 ^ (10 - b))) := by
      have h := Nat.div_add_mod j (2 ^ (10 - b))
      have e : 2 ^ (10 - b) * (j / 2 ^ (10 - b)) =
          2 ^ (9 - b) * (2 * (j / 2 ^ (10 - b))) := by
        rw [hA2]; ring
      omega
    conv_lhs => rw [hdec]
    rw [Nat.add_mul_div_left _ _ htpos]
    ring
  have hval : j - j % 2 ^ (9 - b) = 2 ^ (9 - b) * (j / 2 ^ (9 - b)) := by
    have h := Nat.div_add_mod j (2 ^ (9 - b))
    omega
  have hrt2 : j % 2 ^ (10 - b) / 2 ^ (9 - b) < 2 := by
    rw [Nat.div_lt_iff_lt_mul htpos, ← hA2]
    exact hrlt
  rw [hval, hjt]
  by_cases hr' : 2 ^ (9 - b) ≤ j % 2 ^ (10 - b)
  · have hrt : j % 2 ^ (10 - b) / 2 ^ (9 - b) = 1 := by
      have h1 : 1 ≤ j % 2 ^ (10 - b) / 2 ^ (9 - b) := by
        rw [Nat.le_div_iff_mul_le htpos]
        simpa using hr'
      omega
    rw [if_pos (hQj.mpr hr'), hrt, hP, hA2]
    ring
  · have hrt : j % 2 ^ (10 - b) / 2 ^ (9 - b) = 0 := by
      exact Nat.div_eq_of_lt (by omega)
    rw [if_neg (fun h => hr' (hQj.mp h)), hrt, hP, hA2]
    ring

private theorem bitStep_two_pow (j : Nat) {b pos : Nat} (hb : b ≤ 9)
    (hpos : pos = j - j % 2 ^ (10 - b)) :
    bitStep (2 ^ j) b pos = j - j % 2 ^ (9 - b) := by
  subst hpos
  unfold bitStep
  rw [hypBits_letN_eq, hypBits_letN_eq]
  by_cases hq : j - j % 2 ^ (10 - b) + 2 ^ (9 - b) ≤ j
  · have hne : (2 ^ j >>> (j - j % 2 ^ (10 - b) + 2 ^ (9 - b))) ≠ 0 :=
      (pow_shiftRight_ne_zero j _).mpr hq
    have hb0 : Nat.beq (2 ^ j >>> (j - j % 2 ^ (10 - b) + 2 ^ (9 - b))) 0 = false := by
      rw [← Bool.not_eq_true]
      intro h
      rw [Nat.beq_eq] at h
      exact hne h
    rw [hb0]
    change j - j % 2 ^ (10 - b) + 2 ^ (9 - b) = j - j % 2 ^ (9 - b)
    have h := bitStep_arith j b hb
    rw [if_pos hq] at h
    exact h
  · have hz : (2 ^ j >>> (j - j % 2 ^ (10 - b) + 2 ^ (9 - b))) = 0 := by
      by_contra h
      exact hq ((pow_shiftRight_ne_zero j _).mp h)
    have hb1 : Nat.beq (2 ^ j >>> (j - j % 2 ^ (10 - b) + 2 ^ (9 - b))) 0 = true := by
      rw [Nat.beq_eq]
      exact hz
    rw [hb1]
    change j - j % 2 ^ (10 - b) = j - j % 2 ^ (9 - b)
    have h := bitStep_arith j b hb
    rw [if_neg hq] at h
    exact h

private theorem bitPosK_aux (j : Nat) (hj : j < 1024) :
    ∀ b ≤ 10, Nat.rec 0 (bitStep (2 ^ j)) b = j - j % 2 ^ (10 - b) := by
  intro b
  induction b with
  | zero =>
    intro _
    show (0 : Nat) = j - j % 2 ^ (10 - 0)
    rw [Nat.mod_eq_of_lt (by norm_num; omega : j < 2 ^ 10)]
    simp
  | succ m ih =>
    intro hm
    have hm' : m ≤ 10 := by omega
    have hm9 : m ≤ 9 := by omega
    rw [show Nat.rec 0 (bitStep (2 ^ j)) (m + 1) =
      bitStep (2 ^ j) m (Nat.rec 0 (bitStep (2 ^ j)) m) from rfl, ih hm']
    have e : 10 - (m + 1) = 9 - m := by omega
    rw [e]
    exact bitStep_two_pow j hm9 rfl

theorem bitPosK_two_pow {j : Nat} (hj : j < 1024) : bitPosK (2 ^ j) = j := by
  have h := bitPosK_aux j hj 10 le_rfl
  have hk : bitPosK (2 ^ j) = Nat.rec 0 (bitStep (2 ^ j)) 10 := rfl
  rw [hk, h]
  rw [show (2 : Nat) ^ (10 - 10) = 1 from by norm_num, Nat.mod_one, Nat.sub_zero]

theorem range_filter_testBit_eq_nil {C : Nat} (hC : C < 2 ^ 1024) :
    ((List.range 1024).filter fun j => C.testBit j) = [] ↔ C = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 1024
    · have hfi : C.testBit i = false := by
        have := (List.filter_eq_nil_iff.1 h) i (List.mem_range.2 hi)
        simpa [Bool.not_eq_true] using this
      rw [hfi, Nat.zero_testBit]
    · have hlt : C < 2 ^ i :=
        lt_of_lt_of_le hC (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hlt, Nat.zero_testBit]
  · intro h
    subst h
    simp [Nat.zero_testBit]

private theorem range_filter_testBit_two_pow_aux : ∀ n j, j < n →
    (List.range n).filter (fun i => (2 ^ j).testBit i) = [j]
  | 0, j, hj => by omega
  | Nat.succ n, j, hj => by
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hlt | heq
    · rw [range_filter_testBit_two_pow_aux n j hlt]
      have hfalse : (2 ^ j).testBit n = false := Nat.testBit_two_pow_of_ne (by omega)
      simp [hfalse]
    · rw [heq]
      have hnil : (List.range n).filter (fun i => (2 ^ n).testBit i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i hi
        rw [Nat.testBit_two_pow]
        simp [show n ≠ i from (Nat.ne_of_lt (List.mem_range.1 hi)).symm]
      rw [hnil]
      simp [Nat.testBit_two_pow]

private theorem range_filter_testBit_two_pow {j n : Nat} (hj : j < n) :
    (List.range n).filter (fun i => (2 ^ j).testBit i) = [j] :=
  range_filter_testBit_two_pow_aux n j hj

theorem range_filter_testBit_eq_singleton {C j : Nat} (hC : C < 2 ^ 1024) :
    ((List.range 1024).filter fun i => C.testBit i) = [j] ↔ C = 2 ^ j := by
  constructor
  · intro h
    have hjmem : j ∈ (List.range 1024).filter (fun i => C.testBit i) := by rw [h]; simp
    have hj : j < 1024 := List.mem_range.1 (List.mem_filter.1 hjmem).1
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 1024
    · have hiff : C.testBit i = true ↔ i = j := by
        have hm : i ∈ (List.range 1024).filter (fun i => C.testBit i) ↔ i ∈ [j] := by rw [h]
        rw [List.mem_filter, List.mem_range, List.mem_singleton] at hm
        exact ⟨fun hci => (hm.1 ⟨hi, hci⟩), fun hij => (hm.2 hij).2⟩
      rw [Nat.testBit_two_pow]
      by_cases hci : C.testBit i = true
      · have : j = i := (hiff.1 hci).symm
        simp [hci, this]
      · have hci' : C.testBit i = false := by simpa [Bool.not_eq_true] using hci
        have hji : j ≠ i := fun hji => hci (hiff.2 hji.symm)
        simp [hci', hji]
    · have hlt : C < 2 ^ i :=
        lt_of_lt_of_le hC (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hji : j ≠ i := by omega
      rw [Nat.testBit_lt_two_pow hlt, Nat.testBit_two_pow_of_ne hji]
  · intro h
    subst h
    have hj : j < 1024 := by
      by_contra hge
      have : 2 ^ 1024 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact range_filter_testBit_two_pow hj

theorem land_sub_one_eq_zero_iff {C : Nat} (hC : C ≠ 0) :
    C &&& (C - 1) = 0 ↔ ∃ j, C = 2 ^ j :=
  Nat.and_sub_one_eq_zero_iff_isPowerOfTwo hC

end CFSG.KC.Misc.Hyp

end
