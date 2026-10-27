module

public import CFSG.Certificates.Kernel.Misc.Sp6SndLin
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.Misc.Sp6.Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6
open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_lt)

private theorem mul_bitK (a k x : ℕ) : Nat.mul (bitK a k) x = if a.testBit k then x else 0 := by
  rw [bitK_eq]; split_ifs <;> simp

private theorem mul_bitK' (a k x : ℕ) : bitK a k * x = if a.testBit k then x else 0 :=
  mul_bitK a k x

private theorem outerK_eq (a b : ℕ) : outerK a b = outer a b := by
  unfold outerK
  rw [letN_eq]
  show Nat.xor (Nat.xor (Nat.mul (bitK a 0) _) (Nat.mul (bitK a 1) _)) (Nat.mul (bitK a 2) _) = _
  rw [mul_bitK, mul_bitK, mul_bitK]
  rfl

private theorem outer_lt (a b : ℕ) : outer a b < 512 := by
  have h1 : (b &&& 7) < 8 := by
    have := Nat.and_le_right (n := b) (m := 7); omega
  unfold outer
  have e1 : ∀ s : ℕ, (if a.testBit s then (b &&& 7) <<< (3 * s) else 0) < 512 ∨ s ≥ 3 := by
    intro s
    by_cases hs : s < 3
    · left
      split_ifs
      · rw [Nat.shiftLeft_eq]
        interval_cases s <;> simp <;> omega
      · omega
    · right; omega
  have a0 := e1 0
  have a1 := e1 1
  have a2 := e1 2
  simp only [Nat.mul_zero, Nat.shiftLeft_zero] at a0
  simp only [Nat.mul_one] at a1
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  rw [h512]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
  · rcases a0 with h | h
    · rw [h512] at h; exact h
    · omega
  · rcases a1 with h | h
    · rw [h512] at h; exact h
    · omega
  · rcases a2 with h | h
    · rw [h512] at h; exact h
    · omega

theorem qK_eq (u : Bool) (v : ℕ) : qK (if u then 1 else 0) v = qOf u v := by
  unfold qK
  rw [letN_eq, letN_eq, letN_eq]
  show Nat.xor (Nat.xor (outerK (wpart v) (wpart v)) (outerK (wpart v) (xpart v)))
    (Nat.mul _ (outerK (xpart v) (xpart v))) = _
  rw [outerK_eq, outerK_eq, outerK_eq]
  cases u <;> simp [qOf] <;> rfl

private theorem qOf_zero (u : Bool) : qOf u 0 = 0 := by
  cases u <;> simp [qOf, wpart, xpart, outer]

private theorem qOf_lt (u : Bool) (v : ℕ) : qOf u v < 512 := by
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  unfold qOf
  rw [h512]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
  · have := outer_lt (wpart v) (wpart v); omega
  · have := outer_lt (wpart v) (xpart v); omega
  · split_ifs
    · have := outer_lt (xpart v) (xpart v); omega
    · omega

private theorem mkv_lt (w x : ℕ) : mkv w x < 64 := by
  have hw1 := Nat.and_le_right (n := w) (m := 1)
  have hw2 := Nat.and_le_right (n := w) (m := 2)
  have hw4 := Nat.and_le_right (n := w) (m := 4)
  have hx1 := Nat.and_le_right (n := x) (m := 1)
  have hx2 := Nat.and_le_right (n := x) (m := 2)
  have hx4 := Nat.and_le_right (n := x) (m := 4)
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  unfold mkv
  rw [h64]
  simp only [Nat.shiftLeft_eq]
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
    (Nat.or_lt_two_pow ?_ ?_) ?_) ?_) ?_) ?_ <;> norm_num <;> omega

private theorem lane9_testBit (B k i : ℕ) :
    (lane9 B k).testBit i = (decide (i < 9) && B.testBit (9 * k + i)) := by
  unfold lane9
  show ((B >>> (9 * k)) &&& 511).testBit i = _
  have h : (511 : ℕ) = 2 ^ 9 - 1 := by norm_num
  rw [h, Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  exact Bool.and_comm _ _

private theorem lane9_zero (k : ℕ) : lane9 0 k = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [lane9_testBit]; simp

private theorem lane9_lor_shift (X y p k : ℕ) (hy : y < 512) :
    lane9 (X ||| (y <<< (9 * p))) k = lane9 X k ||| (if k = p then y else 0) := by
  have hy' : ∀ i, 9 ≤ i → y.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy
      (by calc (512 : ℕ) = 2 ^ 9 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi))
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [lane9_testBit, Nat.testBit_lor, Nat.testBit_lor, lane9_testBit, Nat.testBit_shiftLeft]
  by_cases hi : i < 9
  · by_cases hk : k = p
    · subst hk
      simp [hi]
    · have h0 : (if k = p then y else 0) = 0 := if_neg hk
      rw [h0]
      by_cases h9 : 9 * p ≤ 9 * k + i
      · have : 9 ≤ 9 * k + i - 9 * p := by omega
        simp [hi, hy' _ this]
      · simp [hi, h9]
  · have h1 : (if k = p then y else 0).testBit i = false := by
      split_ifs
      · exact hy' i (by omega)
      · simp
    rw [h1]; simp [hi]

private theorem shl_one (i : ℕ) : Nat.shiftLeft 1 i = 2 ^ i := by
  show 1 <<< i = 2 ^ i
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem qImg_eq (u : Bool) (A : ℕ) {v : ℕ} (hv : v < 64) :
    qImg (if u then 1 else 0) (tLo A) (tHi A) v = qOf u (evalV (dec A) v) := by
  unfold qImg
  rw [qK_eq, actT_eq A hv]

private theorem mkvK_eq (w x : ℕ) : mkvK w x = mkv w x := by
  unfold mkvK mkv
  simp only [Nat.land_eq, Nat.lor_eq, Nat.or_assoc]
  rfl

private theorem qImg_mkv (u : Bool) (A w x : ℕ) :
    qImg (if u then 1 else 0) (tLo A) (tHi A) (mkvK w x) = qOf u (evalV (dec A) (mkv w x)) :=
  by rw [mkvK_eq]; exact qImg_eq u A (mkv_lt w x)

private theorem qImg_lt (u : Bool) (A v : ℕ) : qImg (if u then 1 else 0) (tLo A) (tHi A) v < 512 := by
  unfold qImg
  rw [qK_eq]; exact qOf_lt _ _

private theorem bEntry_lt (u : Bool) (A i j : ℕ) :
    bEntry (if u then 1 else 0) (tLo A) (tHi A) i j < 512 := by
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  unfold bEntry
  generalize Nat.beq i j = b
  cases b
  · dsimp only
    rw [h512]
    refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow ?_ ?_) ?_
    · have := qImg_lt u A (mkvK (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j)); omega
    · have := qImg_lt u A (mkvK (Nat.shiftLeft 1 i) 0); omega
    · have key : ∀ m x : ℕ, m ≤ 1 → x < 2 ^ 9 → Nat.mul m x < 2 ^ 9 := fun m x hm hx => by
        interval_cases m <;> simp <;> omega
      have := qImg_lt u A (mkvK 0 (Nat.shiftLeft 1 j))
      exact key _ _ (by split_ifs <;> omega) (by omega)
  · exact qImg_lt u A _

private theorem bEntry_eq (u : Bool) (A : ℕ) {i j : ℕ} (hi : i < 3) (hj : j < 3) :
    bEntry (if u then 1 else 0) (tLo A) (tHi A) i j = (bOf u (dec A)).getD (3 * i + j) 0 := by
  have hget : (bOf u (dec A)).getD (3 * i + j) 0 = if i = j then
      qOf u (evalV (dec A) (mkv (2 ^ i) 0)) else
      qOf u (evalV (dec A) (mkv (2 ^ i) (2 ^ j))) ^^^ qOf u (evalV (dec A) (mkv (2 ^ i) 0)) ^^^
        (if u then qOf u (evalV (dec A) (mkv 0 (2 ^ j))) else 0) := by
    have h1 : (3 * i + j) / 3 = i := by omega
    have h2 : (3 * i + j) % 3 = j := by omega
    have h3 : 3 * i + j < 9 := by omega
    rw [List.getD_eq_getElem?_getD]
    unfold bOf spanW
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_range h3]
    simp only [Option.map_some, Option.getD_some, h1, h2]
    by_cases hij : i = j
    · simp [hij, qOf_zero, evalV_zero']
    · cases u <;> simp [hij, qOf_zero, evalV_zero']
  rw [hget]
  unfold bEntry
  simp only [shl_one]
  have hv1 := mkv_lt (2 ^ i) (2 ^ j)
  have hv2 := mkv_lt (2 ^ i) 0
  have hv3 := mkv_lt 0 (2 ^ j)
  by_cases hij : i = j
  · subst hij
    rw [Nat.beq_refl, if_pos rfl]
    show qImg _ _ _ _ = _
    exact qImg_mkv u A _ _
  · have hb : Nat.beq i j = false := by
      cases h : Nat.beq i j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hij
    rw [hb]
    rw [if_neg hij]
    show Nat.xor (Nat.xor (qImg _ _ _ _) (qImg _ _ _ _)) (Nat.mul _ (qImg _ _ _ _)) = _
    rw [qImg_mkv, qImg_mkv, qImg_mkv]
    cases u <;> simp <;> rfl

private theorem bTabK_eq (m T₀ T₁ : ℕ) : bTabK m T₀ T₁ = (((((((((0 ||| (bEntry m T₀ T₁ 0 0 <<< (9 * (3 * 0 + 0)))) ||| (bEntry m T₀ T₁ 0 1 <<< (9 * (3 * 0 + 1)))) ||| (bEntry m T₀ T₁ 0 2 <<< (9 * (3 * 0 + 2)))) ||| (bEntry m T₀ T₁ 1 0 <<< (9 * (3 * 1 + 0)))) ||| (bEntry m T₀ T₁ 1 1 <<< (9 * (3 * 1 + 1)))) ||| (bEntry m T₀ T₁ 1 2 <<< (9 * (3 * 1 + 2)))) ||| (bEntry m T₀ T₁ 2 0 <<< (9 * (3 * 2 + 0)))) ||| (bEntry m T₀ T₁ 2 1 <<< (9 * (3 * 2 + 1)))) ||| (bEntry m T₀ T₁ 2 2 <<< (9 * (3 * 2 + 2)))) := rfl

theorem lane9_bTabK (u : Bool) (A : ℕ) {k : ℕ} (hk : k < 9) :
    lane9 (bTabK (if u then 1 else 0) (tLo A) (tHi A)) k = (bOf u (dec A)).getD k 0 := by
  rw [bTabK_eq]
  have hl := bEntry_lt u A
  simp only [lane9_lor_shift _ _ _ _ (hl _ _), lane9_zero]
  interval_cases k
  all_goals (simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceEqDiff, Nat.zero_or, Nat.or_zero, if_true, if_false, Nat.succ_ne_self, OfNat.ofNat_ne_zero, one_ne_zero]; exact bEntry_eq u A (by norm_num) (by norm_num))

private theorem rec_xor_eq (F : ℕ → ℕ) (e n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => acc ^^^ bitK e k * F k) n : ℕ) =
      xorBits n F e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, ← ih]
    show _ ^^^ (bitK e n * F n) = _
    rw [mul_bitK']

private theorem xorBits_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) (v : ℕ) :
    xorBits n f v = xorBits n g v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem evalEK_xor (B e : ℕ) : evalEK B e = xorBits 9 (lane9 B) e :=
  rec_xor_eq _ _ 9

theorem evalEK_eq (u : Bool) (A e : ℕ) :
    evalEK (bTabK (if u then 1 else 0) (tLo A) (tHi A)) e = evalE (bOf u (dec A)) e := by
  rw [evalEK_xor]
  unfold evalE
  exact xorBits_congr (fun j hj => lane9_bTabK u A hj) e

theorem validK_eq (u : Bool) (A : ℕ) : validK (if u then 1 else 0) A = validT u (dec A) := by
  unfold validK
  simp only [letB_eq]
  apply Bool.eq_iff_iff.mpr
  rw [allN_eq_true]
  have hlen := (dec_tup A).1
  have hall := (dec_tup A).2
  unfold validT
  simp only [hlen, hall, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne, ne_eq, true_and]
  have hall' : (∀ x ∈ dec A, x < 64) = True := eq_true hall
  simp only [hall', true_and]
  have hb : ∀ a b : ℕ, Nat.beq a b = true ↔ a = b :=
    fun a b => ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩
  have key : ∀ i < 64, (andB (orB (i.beq 0) (notB ((actT (tLo A) (tHi A) i).beq 0)))
          ((qK (if u = true then 1 else 0) (actT (tLo A) (tHi A) i)).beq
            (evalEK (bTabK (if u = true then 1 else 0) (tLo A) (tHi A))
              (qK (if u = true then 1 else 0) i))) = true) ↔
      ((i == 0 || evalV (dec A) i != 0) = true ∧
        qOf u (evalV (dec A) i) = evalE (bOf u (dec A)) (qOf u i)) := by
    intro i hi
    rw [andB_eq_true, orB_eq_true, notB_eq_true, actT_eq A hi, qK_eq, qK_eq, evalEK_eq, hb, hb]
    have : Nat.beq (evalV (dec A) i) 0 = false ↔ evalV (dec A) i ≠ 0 := by
      cases h : Nat.beq (evalV (dec A) i) 0
      · simp only [true_iff]; intro h0; simp [(hb _ _).2 h0] at h
      · simp only [Bool.true_eq_false, false_iff, not_not]; exact (hb _ _).1 h
    rw [this]
    simp
  rw [forall₂_congr key]
  constructor
  · intro h; exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩
  · rintro ⟨h1, h2⟩ x hx; exact ⟨h1 x hx, h2 x hx⟩

private theorem nbeq_iff (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

private theorem rec_bitset (S : ℕ → ℕ → ℕ) (p : ℕ → Bool)
    (hS : ∀ e acc, S e acc = acc ||| (if p e then 1 <<< e else 0)) (n v : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 S n : ℕ).testBit v = (decide (v < n) && p v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (S n (Nat.rec 0 S n)).testBit v = _
    rw [hS, Nat.testBit_lor, ih]
    have h1 : (1 <<< n).testBit v = decide (n = v) := by
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    rcases lt_trichotomy v n with h | h | h
    · have : n ≠ v := by omega
      cases hp : p n <;> simp [h1, hp, h, this, show v < n + 1 by omega]
    · subst h
      cases hp : p v <;> simp [h1, hp]
    · have : n ≠ v := by omega
      cases hp : p n <;> simp [h1, hp, show ¬ v < n by omega, show ¬ v < n + 1 by omega, this]

set_option maxRecDepth 10000 in
theorem xeK_testBit (j e : ℕ) : (xeK j).testBit e = (decide (e < 512) && e.testBit j) := by
  unfold xeK
  exact rec_bitset (fun e acc => Nat.lor acc (Nat.mul (bitK e j) (Nat.shiftLeft 1 e)))
    (fun e => e.testBit j) (fun e acc => by rw [mul_bitK]; rfl) (nat_lit 512) e

theorem xvK_testBit (j v : ℕ) : (xvK j).testBit v = (decide (v < 64) && v.testBit j) := by
  unfold xvK
  exact rec_bitset (fun e acc => Nat.lor acc (Nat.mul (bitK e j) (Nat.shiftLeft 1 e)))
    (fun e => e.testBit j) (fun e acc => by rw [mul_bitK]; rfl) (nat_lit 64) v

theorem q0K_testBit (u : Bool) (v : ℕ) :
    (q0K (if u then 1 else 0)).testBit v = (decide (v < 64) && qOf u v == 0) := by
  unfold q0K
  refine rec_bitset (fun e acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.lor acc (Nat.shiftLeft 1 e))
    (Nat.beq (qK (if u then 1 else 0) e) 0)) (fun e => qOf u e == 0) (fun e acc => ?_) (nat_lit 64) v
  rw [qK_eq]
  cases h : Nat.beq (qOf u e) 0
  · have : ¬ qOf u e = 0 := fun h0 => by simp [(nbeq_iff _ _).2 h0] at h
    simp [this]
  · have := (nbeq_iff _ _).1 h
    simp [this]

private theorem mul_bitK_testBit (a k x i : ℕ) :
    (Nat.mul (bitK a k) x).testBit i = (a.testBit k && x.testBit i) := by
  rw [mul_bitK]; split_ifs with h <;> simp [h]

private theorem fixRec_inner (N S : ℕ) (X F : ℕ → ℕ)
    (hX : ∀ j < N, ∀ e, (X j).testBit e = (decide (e < S) && e.testBit j)) (i e : ℕ) (he : e < S) :
    ∀ m ≤ N, (Nat.rec (motive := fun _ => ℕ) 0
        (fun j y => Nat.xor y (Nat.mul (bitK (F j) i) (X j))) m : ℕ).testBit e =
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => Nat.xor acc (Nat.mul (bitK e k) (F k))) m : ℕ).testBit i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    show Nat.testBit (_ ^^^ _) e = Nat.testBit (_ ^^^ _) i
    rw [Nat.testBit_xor, Nat.testBit_xor, ih (by omega), mul_bitK_testBit, mul_bitK_testBit,
      hX m (by omega)]
    cases (F m).testBit i <;> cases e.testBit m <;> simp [he]

private theorem fixRec_testBit (N S : ℕ) (hS : S = 2 ^ N) (X F : ℕ → ℕ)
    (hX : ∀ j < N, ∀ e, (X j).testBit e = (decide (e < S) && e.testBit j)) (e : ℕ) :
    ∀ n ≤ N, (Nat.rec (motive := fun _ => ℕ) (Nat.sub (Nat.shiftLeft 1 S) 1)
      (fun i acc => letN (Nat.rec (motive := fun _ => ℕ) 0
        (fun j y => Nat.xor y (Nat.mul (bitK (F j) i) (X j))) N) fun Y =>
        Nat.land acc (Nat.sub (Nat.sub (Nat.shiftLeft 1 S) 1) (Nat.xor Y (X i)))) n : ℕ).testBit e
        = true ↔ e < S ∧ ∀ i < n,
      (Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => Nat.xor acc (Nat.mul (bitK e k) (F k))) N : ℕ).testBit i = e.testBit i := by
  have hXlt : ∀ j < N, X j < 2 ^ S := fun j hj => Nat.lt_pow_two_of_testBit _ (fun e he => by
    rw [hX j hj]; have : ¬ e < S := by omega
    simp [this])
  have hY : ∀ i, ∀ m ≤ N, (Nat.rec (motive := fun _ => ℕ) 0
      (fun j y => Nat.xor y (Nat.mul (bitK (F j) i) (X j))) m : ℕ) < 2 ^ S := by
    intro i m
    induction m with
    | zero => intro _; exact Nat.two_pow_pos _
    | succ m ih =>
      intro hm
      show (_ ^^^ _) < 2 ^ S
      refine Nat.xor_lt_two_pow (ih (by omega)) ?_
      rw [mul_bitK]
      split_ifs
      · exact hXlt m (by omega)
      · exact Nat.two_pow_pos _
  intro n
  induction n with
  | zero =>
    intro _
    show ((Nat.shiftLeft 1 S) - 1).testBit e = true ↔ _
    rw [shl_one, Nat.testBit_two_pow_sub_one]
    simp
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    have hrec : ∀ (z : ℕ) (s : ℕ → ℕ → ℕ) (n : ℕ),
        (Nat.rec (motive := fun _ => ℕ) z s (n + 1) : ℕ) = s n (Nat.rec z s n) := fun _ _ _ => rfl
    simp only [hrec, letN_eq] at ih ⊢
    have hW : ∀ w : ℕ, Nat.sub (Nat.sub (Nat.shiftLeft 1 S) 1) w = 2 ^ S - (w + 1) := by
      intro w
      show Nat.shiftLeft 1 S - 1 - w = _
      rw [shl_one, Nat.sub_sub, Nat.add_comm 1 w]
    rw [hW]
    show Nat.testBit (_ &&& _) e = true ↔ _
    rw [Nat.testBit_land, Bool.and_eq_true, ih]
    by_cases he : e < S
    · have hw : (Nat.xor (Nat.rec (motive := fun _ => ℕ) 0
          (fun j y => Nat.xor y (Nat.mul (bitK (F j) n) (X j))) N : ℕ) (X n)).testBit e =
          (!((Nat.rec (motive := fun _ => ℕ) 0
          (fun k acc => Nat.xor acc (Nat.mul (bitK e k) (F k))) N : ℕ).testBit n == e.testBit n)) := by
        show Nat.testBit (_ ^^^ _) e = _
        rw [Nat.testBit_xor, fixRec_inner N S X F hX n e he N le_rfl, hX n (by omega)]
        cases (Nat.rec (motive := fun _ => ℕ) 0
          (fun k acc => Nat.xor acc (Nat.mul (bitK e k) (F k))) N : ℕ).testBit n <;>
          cases e.testBit n <;> simp [he]
      have hwlt : Nat.xor (Nat.rec (motive := fun _ => ℕ) 0
          (fun j y => Nat.xor y (Nat.mul (bitK (F j) n) (X j))) N : ℕ) (X n) < 2 ^ S :=
        Nat.xor_lt_two_pow (hY n N le_rfl) (hXlt n (by omega))
      rw [Nat.testBit_two_pow_sub_succ hwlt e, hw]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        refine ⟨he, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact h2 i h
        · subst h; simpa [he] using h3
      · rintro ⟨_, h2⟩
        refine ⟨⟨he, fun i hi => h2 i (by omega)⟩, ?_⟩
        have := h2 n (by omega)
        simpa [he] using this
    · simp [he]

private theorem bits_eq_iff (N a b : ℕ) (ha : a < 2 ^ N) (hb : b < 2 ^ N) :
    a = b ↔ ∀ i < N, a.testBit i = b.testBit i := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    by_cases hi : i < N
    · exact h i hi
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

private theorem fix_final (N S : ℕ) (hS : S = 2 ^ N) (R e : ℕ) (hR : R < S) :
    (decide (e < S) && R == e) = true ↔ e < S ∧ ∀ i < N, R.testBit i = e.testBit i := by
  subst hS
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨he, rfl⟩
    exact ⟨he, fun _ _ => rfl⟩
  · rintro ⟨he, h⟩
    exact ⟨he, (bits_eq_iff N R e hR he).2 h⟩

private theorem lane9_lt (B k : ℕ) : lane9 B k < 512 := by
  have := Nat.and_le_right (n := B >>> (9 * k)) (m := 511)
  unfold lane9
  show (B >>> (9 * k)) &&& 511 < 512
  omega

private theorem evalEK_lt (B e : ℕ) : evalEK B e < 512 := by
  rw [evalEK_xor]
  exact xorBits_lt (n := 9) (fun j _ => by have := lane9_lt B j; omega) e

theorem fixE_testBit {XE : ℕ → ℕ} (hXE : ∀ j < 9, XE j = xeK j) (B e : ℕ) :
    (fixE XE B).testBit e = (decide (e < 512) && evalEK B e == e) := by
  have key := fixRec_testBit 9 512 (by norm_num) XE (lane9 B)
    (fun j hj e => by rw [hXE j hj, xeK_testBit]) e 9 le_rfl
  rw [Bool.eq_iff_iff, fix_final 9 512 (by norm_num) (evalEK B e) e (evalEK_lt B e)]
  exact key

theorem fixV_testBit {XV : ℕ → ℕ} (hXV : ∀ j < 6, XV j = xvK j) (A v : ℕ) :
    (fixV XV A).testBit v = (decide (v < 64) && evalV (dec A) v == v) := by
  have key := fixRec_testBit 6 64 (by norm_num) XV (imgK A)
    (fun j hj e => by rw [hXV j hj, xvK_testBit]) v 6 le_rfl
  have hR : (Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => Nat.xor acc (Nat.mul (bitK v k) (imgK A k))) 6 : ℕ) = evalV (dec A) v :=
    (rec_xor_eq (imgK A) v 6).trans (xorBits_congr (fun j hj => (getD_dec A hj).symm) v)
  rw [Bool.eq_iff_iff, fix_final 6 64 (by norm_num) (evalV (dec A) v) v
    (evalV_lt' (dec_tup A).2 v)]
  refine key.trans ?_
  rw [hR]

theorem recAnd_testBit (s : ℕ) (F : ℕ → ℕ) (c : ℕ → Bool) (n e : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) s
      (fun i acc => Bool.rec (motive := fun _ => ℕ) acc (Nat.land acc (F i)) (c i)) n).testBit e
      = true ↔ s.testBit e = true ∧ ∀ i < n, c i = true → (F i).testBit e = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (Bool.rec (motive := fun _ => ℕ) _ (Nat.land _ (F n)) (c n)).testBit e = true ↔ _
    cases hc : c n
    · rw [ih]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi hci => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact h2 i h hci
        · subst h; rw [hc] at hci; exact absurd hci (by simp)
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i hi => h2 i (by omega)⟩
    · show (Nat.land _ _).testBit e = true ↔ _
      rw [Nat.land_eq, Nat.testBit_land, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun i hi hci => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact h2 i h hci
        · subst h; exact h3
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 n (by omega) hc⟩

end CFSG.KC.Misc.Sp6.Snd

end
