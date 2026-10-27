module

public import Certificates.Data.Kernel.O8.NodeM
public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.F4M

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

private theorem testBit_orN' (f : ℕ → ℕ) (p : ℕ) : ∀ n,
    (orN n f).testBit p = (List.range n).any fun i => (f i).testBit p
  | 0 => by
    have e : orN 0 f = 0 := rfl
    rw [e]
    simp
  | n + 1 => by
    have e : orN (n + 1) f = f n ||| orN n f := rfl
    rw [e, Nat.testBit_or, testBit_orN' f p n, List.range_succ, List.any_append]
    simp [Bool.or_comm]

private theorem pw2_eq (w : ℕ) : pw2 w = 2 ^ w := by
  rw [pw2]
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem maskN_eq (w : ℕ) : maskN w = 2 ^ w - 1 := by
  rw [maskN, ← pw2_eq]
  rfl

private def bsum (W : ℕ) (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bsum W c n + c n * 2 ^ (W * n)

private theorem bsum_lt {W : ℕ} {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) : ∀ n,
    bsum W c n < 2 ^ (W * n)
  | 0 => by simp [bsum]
  | n + 1 => by
    have h1 := bsum_lt hc n
    have h2 : c n * 2 ^ (W * n) ≤ (2 ^ W - 1) * 2 ^ (W * n) :=
      Nat.mul_le_mul_right _ (by have := hc n; omega)
    have hW : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have e : 2 ^ (W * (n + 1)) = (2 ^ W - 1) * 2 ^ (W * n) + 2 ^ (W * n) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.sub_mul, Nat.one_mul, Nat.mul_comm (2 ^ (W * n))]
      have : 2 ^ (W * n) ≤ 2 ^ W * 2 ^ (W * n) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [bsum, e]
    omega

private theorem testBit_bsum {W : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) (p : ℕ) :
    ∀ n, (bsum W c n).testBit p = (decide (p < W * n) && (c (p / W)).testBit (p % W))
  | 0 => by simp [bsum]
  | n + 1 => by
    rw [bsum, Nat.add_comm, Nat.mul_comm (c n),
      Nat.testBit_two_pow_mul_add _ (bsum_lt hc n)]
    by_cases h : p < W * n
    · simp only [h, ↓reduceIte]
      rw [testBit_bsum hW hc p n]
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

private theorem bsum_add (W : ℕ) (a b : ℕ → ℕ) : ∀ n,
    bsum W a n + bsum W b n = bsum W (fun i => a i + b i) n
  | 0 => rfl
  | n + 1 => by
    rw [bsum, bsum, bsum, ← bsum_add W a b n]
    ring

private theorem bsum_and {W n : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) {M : ℕ}
    (hM : ∀ p, M.testBit p = (decide (p < 2 * W * n) && decide (p % (2 * W) < W))) :
    bsum W c (2 * n) &&& M = bsum (2 * W) (fun B => c (2 * B)) n := by
  have hc2 : ∀ B, c (2 * B) < 2 ^ (2 * W) :=
    fun B => lt_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, testBit_bsum hW hc, hM, testBit_bsum (by omega) hc2]
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

private theorem bsum_shr_and {W n : ℕ} (hW : 0 < W) {c : ℕ → ℕ} (hc : ∀ b, c b < 2 ^ W) {M : ℕ}
    (hM : ∀ p, M.testBit p = (decide (p < 2 * W * n) && decide (p % (2 * W) < W))) :
    (bsum W c (2 * n) >>> W) &&& M = bsum (2 * W) (fun B => c (2 * B + 1)) n := by
  have hc2 : ∀ B, c (2 * B + 1) < 2 ^ (2 * W) :=
    fun B => lt_of_lt_of_le (hc _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_bsum hW hc, hM, testBit_bsum (by omega) hc2]
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

private theorem swarK_getD {k : ℕ} (hk : k < 12) :
    swarK.getD k 0 = orN (4096 / (2 * 2 ^ k)) fun j => (2 ^ 2 ^ k - 1) <<< (2 * 2 ^ k * j) := by
  simp only [swarK, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, pw2_eq, maskN_eq]
  rfl

private theorem div_mul_4096 : ∀ k < 12, 4096 / 2 ^ (k + 1) * 2 ^ (k + 1) = 4096 := by
  decide

theorem testBit_swarK_proved {k : ℕ} (hk : k < 12) (p : ℕ) :
    (swarK.getD k 0).testBit p = (decide (p < 4096) && decide (p % 2 ^ (k + 1) < 2 ^ k)) := by
  rw [swarK_getD hk, testBit_orN']
  have hD : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  rw [hD]
  have hND := div_mul_4096 k hk
  have hDpos : 0 < 2 ^ (k + 1) := by positivity
  have hkD : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hle, hlt⟩
    have e1 : p / 2 ^ (k + 1) = j := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hle)
      (by rw [Nat.succ_mul, Nat.mul_comm]; omega)
    refine ⟨?_, ?_⟩
    · have h1 : (j + 1) * 2 ^ (k + 1) ≤ 4096 / 2 ^ (k + 1) * 2 ^ (k + 1) :=
        Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul, Nat.mul_comm] at h1
      omega
    · rw [Nat.mod_eq_sub_mul_div, e1]
      exact hlt
  · rintro ⟨hp, hr⟩
    refine ⟨p / 2 ^ (k + 1), ?_, Nat.mul_div_le p _, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hDpos, hND]
      exact hp
    · rw [← Nat.mod_eq_sub_mul_div]
      exact hr

private def cnt (x : ℕ) : ℕ → ℕ → ℕ
  | 0, b => (x.testBit b).toNat
  | k + 1, b => cnt x k (2 * b) + cnt x k (2 * b + 1)

private theorem cnt_eq (x : ℕ) : ∀ k b,
    cnt x k b = ((List.range (2 ^ k)).filter fun j => x.testBit (b * 2 ^ k + j)).length
  | 0, b => by
    simp only [cnt, Nat.pow_zero, Nat.mul_one, List.range_one, List.filter_cons, List.filter_nil,
      Nat.add_zero]
    cases x.testBit b <;> rfl
  | k + 1, b => by
    rw [cnt, cnt_eq x k, cnt_eq x k, Nat.pow_succ, Nat.mul_two, List.range_add, List.filter_append,
      List.length_append, List.filter_map, List.length_map]
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

private theorem cnt_le (x k b : ℕ) : cnt x k b ≤ 2 ^ k := by
  rw [cnt_eq]
  exact (List.length_filter_le _ _).trans (by simp)

private theorem cnt_lt (x k b : ℕ) : cnt x k b < 2 ^ 2 ^ k :=
  lt_of_le_of_lt (cnt_le x k b) (Nat.pow_lt_pow_right (by norm_num) Nat.lt_two_pow_self)

private theorem swarK_zipIdx : swarK.zipIdx = (List.range 12).map fun k => (swarK.getD k 0, k) := by
  apply List.ext_getElem
  · simp [swarK]
  · intro i h1 h2
    have hi : i < 12 := by simpa [swarK] using h1
    simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, swarK, List.getElem?_range hi]

private theorem half_4096 : ∀ m < 12, 4096 / 2 ^ m = 2 * (4096 / 2 ^ (m + 1)) := by
  decide

private theorem two_mul_4096 : ∀ m < 12, 2 * 2 ^ m * (4096 / 2 ^ (m + 1)) = 4096 := by
  decide

private theorem step_eq (B S k : ℕ) :
    Nat.add (Nat.land B S) (Nat.land (Nat.shiftRight B k) S) = (B &&& S) + ((B >>> k) &&& S) :=
  rfl

set_option exponentiation.threshold 4096 in
private theorem popc_steps (x : ℕ) (hx : x < 2 ^ 4096) : ∀ m ≤ 12,
    ((List.range m).map fun k => (swarK.getD k 0, k)).foldl
        (fun x p => strictN x fun x =>
          Nat.add (Nat.land x p.1) (Nat.land (Nat.shiftRight x (pw2 p.2)) p.1)) x =
      bsum (2 ^ m) (cnt x m) (4096 / 2 ^ m)
  | 0, _ => by
    simp only [List.range_zero, List.map_nil, List.foldl_nil, Nat.pow_zero, Nat.div_one]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [testBit_bsum (by norm_num) (fun b => by simpa using cnt_lt x 0 b)]
    simp only [Nat.one_mul, Nat.div_one, Nat.mod_one, cnt]
    by_cases hp : p < 4096
    · cases x.testBit p <;> simp [hp]
    · have : x.testBit p = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num)
          (by omega)))
      simp [hp, this]
  | m + 1, hm => by
    rw [List.range_succ, List.map_append, List.foldl_append, popc_steps x hx m (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [strictN_eq', step_eq]
    have hM : ∀ p, (swarK.getD m 0).testBit p =
        (decide (p < 2 * 2 ^ m * (4096 / 2 ^ (m + 1))) &&
          decide (p % (2 * 2 ^ m) < 2 ^ m)) := by
      intro p
      rw [testBit_swarK_proved (by omega), two_mul_4096 m (by omega), ← Nat.pow_succ']
    rw [pw2_eq, half_4096 m (by omega), bsum_and (by positivity) (cnt_lt x m) hM,
      bsum_shr_and (by positivity) (cnt_lt x m) hM, bsum_add, ← Nat.pow_succ']
    rfl

set_option exponentiation.threshold 4096 in
theorem popcM_swarK_proved {x : ℕ} (hx : x < 2 ^ 4096) :
    popcM swarK x = ((List.range 4096).filter fun v => x.testBit v).length := by
  rw [popcM, swarK_zipIdx, popc_steps x hx 12 (Nat.le_refl _)]
  have e : (4096 : ℕ) / 2 ^ 12 = 1 := by norm_num
  rw [e, bsum, bsum, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, cnt_eq]
  simp

end CFSG.KC.O8

end
