module

public import CFSG.Certificates.Kernel.Misc.Sp6SndBase
import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.Misc.Sp6.Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6
open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_zero xorBits_lt)

private theorem xorBits_xor' (n : ℕ) (f : ℕ → ℕ) (v w : ℕ) :
    xorBits n f (v ^^^ w) = xorBits n f v ^^^ xorBits n f w := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, xorBits_succ, ih, Nat.testBit_xor]
    cases v.testBit n <;> cases w.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

private theorem xorBits_map {F : ℕ → ℕ} (hx : ∀ a b, F (a ^^^ b) = F a ^^^ F b) (h0 : F 0 = 0)
    (n : ℕ) (g : ℕ → ℕ) (v : ℕ) : xorBits n (fun j => F (g j)) v = F (xorBits n g v) := by
  induction n with
  | zero => simp [xorBits_zero, h0]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih, hx]
    split_ifs <;> simp [h0]

private theorem xorBits_congr_f {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) (v : ℕ) :
    xorBits n f v = xorBits n g v := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem xorBits_congr_v {n : ℕ} (f : ℕ → ℕ) {v w : ℕ}
    (h : ∀ j < n, v.testBit j = w.testBit j) : xorBits n f v = xorBits n f w := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem xorBits_add (n m : ℕ) (f : ℕ → ℕ) (v : ℕ) :
    xorBits (n + m) f v = xorBits n f v ^^^ xorBits m (fun j => f (n + j)) (v >>> n) := by
  induction m with
  | zero => simp [xorBits_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, xorBits_succ, ih, xorBits_succ, Nat.testBit_shiftRight, Nat.xor_assoc]

private theorem xorBits_pow (n j : ℕ) (f : ℕ → ℕ) :
    xorBits n f (2 ^ j) = if j < n then f j else 0 := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, ih, Nat.testBit_two_pow]
    by_cases h : j = n
    · subst h; simp
    · have h' : n ≠ j := fun e => h e.symm
      simp [h, h']
      split_ifs <;> first | rfl | omega

private theorem xorBits_lt' {n k : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ k) (v : ℕ) :
    xorBits n f v < 2 ^ k := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ]
    refine Nat.xor_lt_two_pow (ih fun j hj => hf j (by omega)) ?_
    split
    · exact hf n (by omega)
    · exact Nat.two_pow_pos k

theorem evalV_xor' (l : List ℕ) (v w : ℕ) : evalV l (v ^^^ w) = evalV l v ^^^ evalV l w :=
  xorBits_xor' 6 _ v w

theorem evalV_zero' (l : List ℕ) : evalV l 0 = 0 := by
  have := evalV_xor' l 0 0
  simp only [Nat.xor_self] at this
  exact this

theorem evalV_lt' {l : List ℕ} (hl : ∀ x ∈ l, x < 64) (v : ℕ) : evalV l v < 64 := by
  have h := xorBits_lt (n := 6) (f := fun j => l.getD j 0) (fun j _ => by
    rw [List.getD_eq_getElem?_getD]
    rcases h : l[j]? with _ | a
    · simp
    · exact hl a (List.mem_of_getElem? h)) v
  exact h

private theorem getD_map_evalV (a b : List ℕ) (j : ℕ) :
    (b.map (evalV a)).getD j 0 = evalV a (b.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases h : b[j]? with _ | x
  · simp [List.getElem?_map, h, evalV_zero']
  · simp [List.getElem?_map, h]

theorem evalV_compT (a b : List ℕ) (v : ℕ) : evalV (compT a b) v = evalV a (evalV b v) := by
  calc evalV (compT a b) v = xorBits 6 (fun j => evalV a (b.getD j 0)) v :=
        xorBits_congr_f (fun j _ => getD_map_evalV a b j) v
    _ = evalV a (xorBits 6 (fun j => b.getD j 0) v) :=
        xorBits_map (F := evalV a) (evalV_xor' a) (evalV_zero' a) 6 _ v

theorem compT_assoc (a b c : List ℕ) : compT (compT a b) c = compT a (compT b c) := by
  unfold compT
  rw [List.map_map]
  refine List.map_congr_left fun x _ => ?_
  exact evalV_compT a b x

theorem idT_tup : IsTup idT := by
  refine ⟨rfl, ?_⟩
  intro x hx
  simp [idT] at hx
  omega

private theorem evalV_pow (l : List ℕ) {j : ℕ} (hj : j < 6) : evalV l (2 ^ j) = l.getD j 0 := by
  unfold evalV
  rw [xorBits_pow]
  simp [hj]

private theorem evalV_idT {x : ℕ} (hx : x < 64) : evalV idT x = x := by
  unfold evalV
  rw [xorBits_congr_f (g := fun j => 2 ^ j)]
  · exact CFSG.EvenSmallLie.OmegaEight.SpBranch.xorBits_two_pow_of_lt (n := 6) hx
  · intro j hj
    interval_cases j <;> rfl

theorem compT_tup {a b : List ℕ} (ha : ∀ x ∈ a, x < 64) (hb : IsTup b) : IsTup (compT a b) := by
  refine ⟨by simp [compT, hb.1], ?_⟩
  intro x hx
  simp only [compT, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact evalV_lt' ha y

theorem idT_compT {b : List ℕ} (hb : IsTup b) : compT idT b = b := by
  unfold compT
  conv_rhs => rw [← List.map_id b]
  refine List.map_congr_left fun x hx => ?_
  exact evalV_idT (hb.2 x hx)

theorem compT_idT {a : List ℕ} (ha : IsTup a) : compT a idT = a := by
  have h6 := ha.1
  refine List.ext_getElem (by simp [compT, idT, h6]) fun j h1 h2 => ?_
  have hj : j < 6 := by simpa [compT, idT] using h1
  have : (compT a idT)[j] = evalV a (2 ^ j) := by
    interval_cases j <;> simp [compT, idT]
  exact this.trans ((evalV_pow a hj).trans (List.getD_eq_getElem _ _ h2))

theorem imgK_lt (A j : ℕ) : imgK A j < 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem dec_tup (A : ℕ) : IsTup (dec A) := by
  refine ⟨by simp [dec], ?_⟩
  intro x hx
  simp only [dec, List.mem_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact imgK_lt A y

theorem getD_dec (A : ℕ) {j : ℕ} (hj : j < 6) : (dec A).getD j 0 = imgK A j := by
  simp [dec, hj]

private theorem lookT_tab3 {c₀ c₁ c₂ : ℕ} (h₀ : c₀ < 64) (h₁ : c₁ < 64) (h₂ : c₂ < 64) {w : ℕ}
    (hw : w < 8) :
    lookT (tab3 c₀ c₁ c₂) w = xorBits 3 (fun j => [c₀, c₁, c₂].getD j 0) w := by
  have b₀ : ∀ m, 6 ≤ m → c₀.testBit m = false := fun m hm =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h₀ (by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm))
  have b₁ : ∀ m, 6 ≤ m → c₁.testBit m = false := fun m hm =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h₁ (by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm))
  have b₂ : ∀ m, 6 ≤ m → c₂.testBit m = false := fun m hm =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h₂ (by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm))
  have hl : ∀ i, (lookT (tab3 c₀ c₁ c₂) w).testBit i =
      (decide (i < 6) && (tab3 c₀ c₁ c₂).testBit (6 * w + i)) := by
    intro i
    show (((tab3 c₀ c₁ c₂) >>> (6 * w)) &&& 63).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight]
    by_cases hi : i < 6
    · have : (63 : ℕ).testBit i = true := by
        rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one]; simpa using hi
      simp [this, hi]
    · have : (63 : ℕ).testBit i = false := by
        rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.testBit_two_pow_sub_one]; simpa using hi
      simp [this, hi]
  have hc₀ : ∀ i, (xorBits 3 (fun j => [c₀, c₁, c₂].getD j 0) w).testBit i = _ := fun i => rfl
  clear hc₀
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [hl]
  have lo : ∀ x, x < 64 → ∀ i, 6 ≤ i → x.testBit i = false := fun x hx i hi =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi))
  have hup : ∀ i, 6 ≤ i → (xorBits 3 (fun j => [c₀, c₁, c₂].getD j 0) w).testBit i = false := by
    intro i hi
    have := xorBits_lt' (n := 3) (k := 6) (f := fun j => [c₀, c₁, c₂].getD j 0) (fun j hj => by
      interval_cases j <;> simp <;> omega) w
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le this
      (Nat.pow_le_pow_right (by norm_num) hi))
  by_cases hi : i < 6
  · simp only [hi, decide_true, Bool.true_and]
    have e : tab3 c₀ c₁ c₂ = (c₀ <<< 6 ||| c₁ <<< 12 ||| ((c₀ ^^^ c₁) <<< 18 ||| c₂ <<< 24)) |||
        ((c₀ ^^^ c₂) <<< 30 ||| (c₁ ^^^ c₂) <<< 36 ||| (c₀ ^^^ c₁ ^^^ c₂) <<< 42) := by
      simp only [tab3, letN_eq]; rfl
    rw [e]
    obtain ⟨R, hR⟩ : ∃ R, xorBits 3 (fun j => [c₀, c₁, c₂].getD j 0) w = R := ⟨_, rfl⟩
    rw [hR]
    clear hl hup
    interval_cases w <;>
      simp only [xorBits_succ, xorBits_zero, Nat.testBit, List.getD_cons_zero,
        List.getD_cons_succ, Nat.reduceShiftRight, Nat.reduceAnd, ite_true, ite_false,
        Nat.zero_xor, Nat.xor_zero, bne_iff_ne, ne_eq, not_true, not_false_eq_true,
        Nat.one_ne_zero, if_true, if_false] at hR <;>
      subst hR <;>
      interval_cases i <;>
      simp only [Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_xor,
        lo c₀ h₀, lo c₁ h₁, lo c₂ h₂, Nat.mul_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceAdd,
        Nat.reduceLeDiff, Nat.reduceSub, decide_true, decide_false, Bool.true_and, Bool.false_and,
        Bool.or_false, Bool.false_or, Bool.xor_false, Bool.false_xor, Nat.zero_testBit,
        Nat.not_le, Nat.reduceLT, Nat.reduceSubDiff,
        Bool.xor_self, Bool.and_false, Bool.or_self, Bool.xor_assoc, ge_iff_le,
        Nat.reduceLeDiff]
  · rw [hup i (by omega)]; simp [hi]

theorem actT_eq (A : ℕ) {v : ℕ} (hv : v < 64) : actT (tLo A) (tHi A) v = evalV (dec A) v := by
  have h7 : v &&& 7 < 8 := Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have h3 : v >>> 3 < 8 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have e1 := lookT_tab3 (imgK_lt A 0) (imgK_lt A 1) (imgK_lt A 2) h7
  have e2 := lookT_tab3 (imgK_lt A 3) (imgK_lt A 4) (imgK_lt A 5) h3
  have e3 : actT (tLo A) (tHi A) v =
      xorBits 3 (fun j => [imgK A 0, imgK A 1, imgK A 2].getD j 0) (v &&& 7) ^^^
        xorBits 3 (fun j => [imgK A 3, imgK A 4, imgK A 5].getD j 0) (v >>> 3) := by
    rw [← e1, ← e2]; rfl
  rw [e3]
  unfold evalV
  rw [show (6 : ℕ) = 3 + 3 from rfl, xorBits_add]
  refine congrArg₂ (· ^^^ ·) ?_ ?_
  · rw [xorBits_congr_v (v := v &&& 7) (w := v)]
    · refine xorBits_congr_f (fun j hj => ?_) v
      rw [getD_dec A (by omega)]
      interval_cases j <;> rfl
    · intro j hj
      rw [Nat.testBit_and]
      have : (7 : ℕ).testBit j = true := by
        rw [show (7 : ℕ) = 2 ^ 3 - 1 by norm_num, Nat.testBit_two_pow_sub_one]; simpa using hj
      simp [this]
  · refine xorBits_congr_f (fun j hj => ?_) _
    rw [getD_dec A (by omega)]
    interval_cases j <;> rfl

end CFSG.KC.Misc.Sp6.Snd

end
