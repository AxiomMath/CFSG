module

public import CFSG.Certificates.Kernel.BabyMonster.SoundDefs
public import CFSG.Certificates.Kernel.BabyMonster.Native.F2n
public import CFSG.Certificates.Kernel.BenesSound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.BM.SL

open CFSG.KC.BM CFSG.KC.YModel
open scoped Matrix

set_option exponentiation.threshold 8192

@[expose] def bz (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem bz_true : bz true = 1 := rfl
@[simp] theorem bz_false : bz false = 0 := rfl

theorem bz_xor (a b : Bool) : bz (a ^^ b) = bz a + bz b := by
  cases a <;> cases b <;> decide

theorem bz_and (a b : Bool) : bz (a && b) = bz a * bz b := by
  cases a <;> cases b <;> decide

theorem bz_inj {a b : Bool} (h : bz a = bz b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem ite_bz (b : Bool) : (if b then (1 : ZMod 2) else 0) = bz b := rfl

theorem bz_decide (p : Prop) [Decidable p] : bz (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, bz]

theorem nxor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem nland (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nlor (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem nshl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem nshr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nmul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nadd (a b : Nat) : Nat.add a b = a + b := rfl
theorem nsub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem ndiv (a b : Nat) : Nat.div a b = a / b := rfl
theorem nmod (a b : Nat) : Nat.mod a b = a % b := rfl

theorem forceB_eq' (v : Nat) (k : Nat → Nat) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

theorem LM_eq : LM = 2 ^ 64 - 1 := by
  unfold LM
  norm_num

theorem M128_eq : (340282366920938463463374607431768211455 : Nat) = 2 ^ 128 - 1 := by
  norm_num

theorem testBit_one' (i : Nat) : (1 : Nat).testBit i = decide (i = 0) := by
  have := @Nat.testBit_two_pow 0 i
  rw [Nat.pow_zero] at this
  rw [this]
  by_cases h : i = 0 <;> simp [h, eq_comm]

theorem mod_sparse {y : Nat} (hy : ∀ p, y.testBit p = true → p % 64 = 0) :
    y % 2 ^ 64 = if y.testBit 0 then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_mod_two_pow]
  by_cases hp : p = 0
  · subst hp
    split <;> simp_all
  · have e : (if y.testBit 0 = true then 1 else 0 : Nat).testBit p = false := by
      split
      · rw [testBit_one']
        simp [hp]
      · simp
    rw [e]
    cases h : y.testBit p
    · simp
    · have := hy p h
      simp only [Bool.and_true, decide_eq_false_iff_not, Nat.not_lt]
      omega

theorem sparse_shr {y : Nat} (hy : ∀ p, y.testBit p = true → p % 64 = 0) :
    ∀ p, (y >>> 64).testBit p = true → p % 64 = 0 := by
  intro p hp
  rw [Nat.testBit_shiftRight] at hp
  have := hy _ hp
  omega

theorem testBit_mul_sparse {c : Nat} (hc : c < 2 ^ 64) :
    ∀ (j y : Nat), (∀ p, y.testBit p = true → p % 64 = 0) → ∀ t, t < 64 →
      (c * y).testBit (64 * j + t) = (c.testBit t && y.testBit (64 * j)) := by
  intro j
  induction j with
  | zero =>
    intro y hy t ht
    have e : c * y = 2 ^ 64 * (c * (y >>> 64)) + c * (y % 2 ^ 64) := by
      rw [Nat.shiftRight_eq_div_pow]
      conv_lhs => rw [← Nat.div_add_mod y (2 ^ 64)]
      ring
    have hlt : c * (y % 2 ^ 64) < 2 ^ 64 := by
      rw [mod_sparse hy]
      split <;> [simpa using hc; simp]
    have h1 : 64 * 0 + t < 64 := by omega
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    simp only [h1, ↓reduceIte]
    rw [mod_sparse hy]
    split <;> simp_all
  | succ j ih =>
    intro y hy t ht
    have e : c * y = 2 ^ 64 * (c * (y >>> 64)) + c * (y % 2 ^ 64) := by
      rw [Nat.shiftRight_eq_div_pow]
      conv_lhs => rw [← Nat.div_add_mod y (2 ^ 64)]
      ring
    have hlt : c * (y % 2 ^ 64) < 2 ^ 64 := by
      rw [mod_sparse hy]
      split <;> [simpa using hc; simp]
    have h1 : ¬ 64 * (j + 1) + t < 64 := by omega
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    simp only [h1, ↓reduceIte]
    have e2 : 64 * (j + 1) + t - 64 = 64 * j + t := by omega
    rw [e2, ih _ (sparse_shr hy) t ht, Nat.testBit_shiftRight]
    have e3 : 64 + 64 * j = 64 * (j + 1) := by omega
    rw [e3]

theorem testBit_mul_sparse_off {c y r : Nat} (hc : c < 2 ^ 64) (hr : r < 64)
    (hy : ∀ p, y.testBit p = true → p % 64 = r) (j t : Nat) (ht : t < 64) :
    (c * y).testBit (64 * j + r + t) = (c.testBit t && y.testBit (64 * j + r)) := by
  have ey : y = (y >>> r) <<< r := by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    by_cases hp : r ≤ p
    · rw [decide_eq_true hp, Bool.true_and, Nat.add_sub_cancel' hp]
    · rw [decide_eq_false hp, Bool.false_and]
      cases h : y.testBit p
      · rfl
      · have := hy p h
        omega
  have hz : ∀ p, (y >>> r).testBit p = true → p % 64 = 0 := by
    intro p hp
    rw [Nat.testBit_shiftRight] at hp
    have := hy _ hp
    omega
  have em : c * y = (c * (y >>> r)) <<< r := by
    conv_lhs => rw [ey]
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_assoc]
  rw [em, Nat.testBit_shiftLeft, decide_eq_true (by omega), Bool.true_and]
  have e1 : 64 * j + r + t - r = 64 * j + t := by omega
  rw [e1, testBit_mul_sparse hc j _ hz t ht, Nat.testBit_shiftRight]
  have e2 : r + 64 * j = 64 * j + r := by omega
  rw [e2]

theorem SMn_eq (n : Nat) : SMn n = 1 * ((2 ^ (64 * n) - 1) / (2 ^ 64 - 1)) := by
  rw [Nat.one_mul, ← LM_eq]
  unfold SMn
  rw [nshl, Nat.one_shiftLeft]
  rfl

theorem testBit_SMn (n q : Nat) :
    (SMn n).testBit q = (decide (q < 64 * n) && decide (q % 64 = 0)) := by
  rw [SMn_eq, CFSG.KC.Benes.testBit_mul_div (by norm_num) rfl (by norm_num), testBit_one']

theorem SMn_sparse (n : Nat) : ∀ p, (SMn n).testBit p = true → p % 64 = 0 := by
  intro p hp
  rw [testBit_SMn] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2

theorem testBit_SMn_mul (n j : Nat) : (SMn n).testBit (64 * j) = decide (j < n) := by
  rw [testBit_SMn]
  by_cases h : j < n
  · simp [h]
  · simp [h]

theorem SM_eq : SM = SMn 4370 := rfl

@[expose] noncomputable def mInner (t SMa SMb : Nat) (Bs : List Nat) (Ac a0 a1 : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ a0 a1 => Nat.xor (Nat.shiftRight a0 t) (Nat.shiftRight a1 (Nat.succ t)))
    (fun T _ ih2 Ac a0 a1 => ih2 (Nat.shiftRight Ac (nat_lit 4096))
        (Nat.xor a0 (Nat.mul (Nat.land Ac LM) (Nat.land T SMa)))
        (Nat.xor a1 (Nat.mul (Nat.shiftRight
          (Nat.land Ac (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64))
          (Nat.land T SMb))))
    Bs Ac a0 a1

@[expose] noncomputable def mRound (S : Nat) (Bs : List Nat) (A u : Nat) : Nat :=
  mInner (Nat.add u u) (Nat.shiftLeft S (Nat.add u u)) (Nat.shiftLeft S (Nat.succ (Nat.add u u))) Bs
    (Nat.shiftRight A (Nat.mul (nat_lit 64) (Nat.add u u))) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def mOuter (S : Nat) (Bs : List Nat) (A m acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun u ih acc => ih (Nat.xor acc (mRound S Bs A u))) m acc

theorem mulSn_eq_mOuter (n : Nat) (Bs : List Nat) (A : Nat) :
    mulSn n Bs A = mOuter (SMn n) Bs A 32 0 := rfl

theorem mOuter_bit (S : Nat) (Bs : List Nat) (A q : Nat) : ∀ m acc,
    bz ((mOuter S Bs A m acc).testBit q) =
      bz (acc.testBit q) + ∑ u ∈ Finset.range m, bz ((mRound S Bs A u).testBit q)
  | 0, acc => by simp [mOuter]
  | m + 1, acc => by
    change bz ((mOuter S Bs A m (Nat.xor acc (mRound S Bs A m))).testBit q) = _
    rw [mOuter_bit S Bs A q m, nxor, Nat.testBit_xor, bz_xor, Finset.sum_range_succ]
    ring

theorem mInner_bit (t SMa SMb : Nat) (q : Nat) : ∀ (Bs : List Nat) (Ac a0 a1 : Nat),
    bz ((mInner t SMa SMb Bs Ac a0 a1).testBit q) =
      bz (a0.testBit (t + q)) + bz (a1.testBit (t + 1 + q)) +
        ∑ s ∈ Finset.range Bs.length,
          (bz ((((Ac >>> (4096 * s)) &&& LM) * (Bs.getD s 0 &&& SMa)).testBit (t + q)) +
           bz (((((Ac >>> (4096 * s)) &&& (2 ^ 128 - 1)) >>> 64) *
              (Bs.getD s 0 &&& SMb)).testBit (t + 1 + q)))
  | [], Ac, a0, a1 => by
    change bz ((Nat.xor (Nat.shiftRight a0 t) (Nat.shiftRight a1 (Nat.succ t))).testBit q) = _
    rw [nxor, nshr, nshr, Nat.testBit_xor, bz_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    simp
  | T :: Bs, Ac, a0, a1 => by
    change bz ((mInner t SMa SMb Bs (Nat.shiftRight Ac 4096)
        (Nat.xor a0 (Nat.mul (Nat.land Ac LM) (Nat.land T SMa)))
        (Nat.xor a1 (Nat.mul (Nat.shiftRight
          (Nat.land Ac 340282366920938463463374607431768211455) 64)
          (Nat.land T SMb)))).testBit q) = _
    rw [mInner_bit t SMa SMb q Bs, List.length_cons, Finset.sum_range_succ']
    simp only [nxor, nshr, nland, nmul, Nat.testBit_xor, bz_xor, M128_eq, List.getD_cons_succ,
      List.getD_cons_zero, Nat.mul_zero, Nat.shiftRight_zero]
    have e : ∀ s, Ac >>> 4096 >>> (4096 * s) = Ac >>> (4096 * (s + 1)) := by
      intro s
      rw [← Nat.shiftRight_add]
      congr 1
      ring
    simp only [e]
    ring

theorem testBit_col (x t : Nat) (ht : t < 64) : (x &&& LM).testBit t = x.testBit t := by
  rw [LM_eq, Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true ht, Bool.and_true]

theorem col_lt (x : Nat) : x &&& LM < 2 ^ 64 := by
  rw [LM_eq]
  exact CFSG.KC.Benes.land_ones_lt x 64

theorem testBit_col2 (x t : Nat) (ht : t < 64) :
    (((x &&& (2 ^ 128 - 1)) >>> 64)).testBit t = x.testBit (64 + t) := by
  rw [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    decide_eq_true (by omega), Bool.and_true]

theorem col2_lt (x : Nat) : (x &&& (2 ^ 128 - 1)) >>> 64 < 2 ^ 64 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    decide_eq_false (by omega), Bool.and_false]

theorem sparse_land_shl {S : Nat} (hS : ∀ p, S.testBit p = true → p % 64 = 0) (T : Nat) {r : Nat}
    (hr : r < 64) : ∀ p, (T &&& (S <<< r)).testBit p = true → p % 64 = r := by
  intro p hp
  rw [Nat.testBit_and, Nat.testBit_shiftLeft] at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  have := hS _ hp.2.2
  omega

theorem testBit_land_shl (S T j r : Nat) :
    (T &&& (S <<< r)).testBit (64 * j + r) = (T.testBit (64 * j + r) && S.testBit (64 * j)) := by
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, decide_eq_true (by omega), Bool.true_and,
    Nat.add_sub_cancel]

theorem term_bit {S : Nat} (hS : ∀ p, S.testBit p = true → p % 64 = 0) {c : Nat} (hc : c < 2 ^ 64)
    (T : Nat) {r : Nat} (hr : r < 64) (j t0 : Nat) (ht0 : t0 < 64) :
    bz ((c * (T &&& (S <<< r))).testBit (r + (64 * j + t0))) =
      bz (c.testBit t0) * bz (T.testBit (64 * j + r)) * bz (S.testBit (64 * j)) := by
  have e : r + (64 * j + t0) = 64 * j + r + t0 := by omega
  rw [e, testBit_mul_sparse_off hc hr (sparse_land_shl hS T hr) j t0 ht0, testBit_land_shl,
    bz_and, bz_and]
  ring

theorem mRound_bit {S : Nat} (hS : ∀ p, S.testBit p = true → p % 64 = 0) (Bs : List Nat)
    (A u j t0 : Nat) (hu : u < 32) (ht0 : t0 < 64) :
    bz ((mRound S Bs A u).testBit (64 * j + t0)) =
      ∑ s ∈ Finset.range Bs.length,
        (bz (A.testBit (64 * (64 * s + (u + u)) + t0)) *
            bz ((Bs.getD s 0).testBit (64 * j + (u + u))) +
          bz (A.testBit (64 * (64 * s + (u + u + 1)) + t0)) *
            bz ((Bs.getD s 0).testBit (64 * j + (u + u + 1)))) * bz (S.testBit (64 * j)) := by
  unfold mRound
  rw [mInner_bit]
  simp only [nadd, nshl, nshr, nmul, Nat.zero_testBit, bz_false, zero_add, Nat.succ_eq_add_one]
  apply Finset.sum_congr rfl
  intro s _
  rw [term_bit hS (col_lt _) _ (by omega) j t0 ht0,
    term_bit hS (col2_lt _) _ (by omega) j t0 ht0, testBit_col _ _ ht0, testBit_col2 _ _ ht0,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight]
  have e1 : 64 * (u + u) + (4096 * s + t0) = 64 * (64 * s + (u + u)) + t0 := by ring
  have e2 : 64 * (u + u) + (4096 * s + (64 + t0)) = 64 * (64 * s + (u + u + 1)) + t0 := by ring
  rw [e1, e2]
  ring

theorem sum_pairs' (h : Nat → ZMod 2) : ∀ m,
    ∑ u ∈ Finset.range m, (h (u + u) + h (u + u + 1)) = ∑ t ∈ Finset.range (m + m), h t
  | 0 => by simp
  | m + 1 => by
    have e : m + 1 + (m + 1) = m + m + 1 + 1 := by omega
    rw [Finset.sum_range_succ, sum_pairs' h m, e, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

theorem sum_pairs (h : Nat → ZMod 2) {m k : Nat} (hk : m + m = k) :
    ∑ u ∈ Finset.range m, (h (u + u) + h (u + u + 1)) = ∑ t ∈ Finset.range k, h t := by
  rw [sum_pairs' h m, hk]

theorem sum_range_mul64 (g : Nat → ZMod 2) : ∀ L,
    ∑ k ∈ Finset.range (64 * L), g k =
      ∑ s ∈ Finset.range L, ∑ t ∈ Finset.range 64, g (64 * s + t)
  | 0 => by simp
  | L + 1 => by
    have e : 64 * (L + 1) = 64 * L + 64 := by ring
    rw [e, Finset.sum_range_add, sum_range_mul64 g L,
      Finset.sum_range_succ (fun s => ∑ t ∈ Finset.range 64, g (64 * s + t)) L]

theorem mulSn_bit (n : Nat) (Bs : List Nat) (A j t : Nat) (ht : t < 64) :
    bz ((mulSn n Bs A).testBit (64 * j + t)) =
      (∑ k ∈ Finset.range (64 * Bs.length),
        bz (A.testBit (64 * k + t)) * bz ((Bs.getD (k / 64) 0).testBit (64 * j + k % 64))) *
        bz (decide (j < n)) := by
  rw [mulSn_eq_mOuter]
  have hSb : (SMn n).testBit (64 * j) = decide (j < n) := testBit_SMn_mul n j
  have hSs := SMn_sparse n
  generalize SMn n = S at hSb hSs ⊢
  rw [mOuter_bit, Nat.zero_testBit, bz_false, zero_add]
  have hr : ∀ u ∈ Finset.range 32, bz ((mRound S Bs A u).testBit (64 * j + t)) = _ :=
    fun u hu => mRound_bit hSs Bs A u j t (Finset.mem_range.1 hu) ht
  rw [Finset.sum_congr rfl hr, Finset.sum_comm, sum_range_mul64 _ Bs.length, Finset.sum_mul, hSb]
  apply Finset.sum_congr rfl
  intro s _
  have hR : ∑ t' ∈ Finset.range 64, bz (A.testBit (64 * (64 * s + t') + t)) *
      bz ((Bs.getD ((64 * s + t') / 64) 0).testBit (64 * j + (64 * s + t') % 64)) =
      ∑ u ∈ Finset.range 32,
        (bz (A.testBit (64 * (64 * s + (u + u)) + t)) *
            bz ((Bs.getD s 0).testBit (64 * j + (u + u))) +
          bz (A.testBit (64 * (64 * s + (u + u + 1)) + t)) *
            bz ((Bs.getD s 0).testBit (64 * j + (u + u + 1)))) := by
    rw [sum_pairs (fun t' => bz (A.testBit (64 * (64 * s + t') + t)) *
      bz ((Bs.getD s 0).testBit (64 * j + t'))) (m := 32) (k := 64) rfl]
    apply Finset.sum_congr rfl
    intro t' ht'
    have ht' := Finset.mem_range.1 ht'
    have e1 : (64 * s + t') / 64 = s := by omega
    have e2 : (64 * s + t') % 64 = t' := by omega
    rw [e1, e2]
  rw [hR, Finset.sum_mul (Finset.range 32) _ (bz (decide (j < n)))]

theorem lget_eq : ∀ (l : List Nat) (i : Nat), lget l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    change lget l i = _
    rw [lget_eq l i, List.getD_cons_succ]

theorem lgetL_eq : ∀ (l : List (List Nat)) (i : Nat), lgetL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    change lgetL l i = _
    rw [lgetL_eq l i, List.getD_cons_succ]

theorem lenL_eq : ∀ (l : List Nat), lenL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenL l) = _
    rw [lenL_eq l, List.length_cons]

theorem lenLL_eq : ∀ (l : List (List Nat)), lenLL l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenLL l) = _
    rw [lenLL_eq l, List.length_cons]

theorem getD_map_of_lt {f : Nat → Nat} {l : List Nat} {i : Nat} (hi : i < l.length) :
    (l.map f).getD i 0 = f (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

@[expose] noncomputable def wfFold (chk : Nat → Nat → Bool) (M : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun s => s)
    (fun T _ ih s => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ s)) (chk T s))
    M s

theorem wfFold_spec (chk : Nat → Nat → Bool) : ∀ (M : List Nat) (s : Nat), wfFold chk M s = 69 →
    M.length + s = 69 ∧ ∀ i < M.length, chk (M.getD i 0) (s + i) = true
  | [], s, h => by
    change s = 69 at h
    simp [h]
  | T :: M, s, h => by
    change Bool.rec (motive := fun _ => Nat) 100000 (wfFold chk M (Nat.succ s)) (chk T s) = 69 at h
    cases hc : chk T s
    · rw [hc] at h
      change (100000 : Nat) = 69 at h
      exact absurd h (by decide)
    · rw [hc] at h
      obtain ⟨h1, h2⟩ := wfFold_spec chk M (s + 1) h
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      intro i hi
      cases i with
      | zero => simpa using hc
      | succ i =>
        rw [List.getD_cons_succ]
        have := h2 i (by simp at hi; omega)
        rwa [Nat.add_assoc, Nat.add_comm 1 i] at this

theorem rowsSn_eq (n s : Nat) : rowsSn n s = min 64 (n - 64 * s) := by
  unfold rowsSn
  change Bool.rec (motive := fun _ => Nat) 64 (n - 64 * s) (Nat.ble (n - 64 * s) 64) = _
  cases h : Nat.ble (n - 64 * s) 64
  · have := Nat.not_le_of_not_ble_eq_true (by rw [h]; decide)
    simp only
    omega
  · have := Nat.le_of_ble_eq_true h
    simp only
    omega

theorem testBit_mask (n r q : Nat) (hr : r ≤ 64) :
    (Nat.mul (SMn n) (Nat.sub (Nat.shiftLeft 1 r) 1)).testBit q =
      (decide (q < 64 * n) && decide (q % 64 < r)) := by
  rw [nmul, nsub, nshl, Nat.one_shiftLeft, SMn_eq, Nat.one_mul, Nat.mul_comm,
    CFSG.KC.Benes.testBit_mul_div (by norm_num) rfl
      (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos r) Nat.one_pos)
        (Nat.pow_le_pow_right (by norm_num) hr)), Nat.testBit_two_pow_sub_one]

theorem wf_bit {n : Nat} {M : List Nat} (h : wfMatn n M = true) :
    M.length = 69 ∧ ∀ s q, (lget M s).testBit q = true → q < 64 * n ∧ q % 64 < rowsSn n s := by
  have h' := Nat.eq_of_beq_eq_true h
  obtain ⟨hl, hc⟩ := wfFold_spec _ M 0 h'
  refine ⟨by omega, ?_⟩
  intro s q hq
  rw [lget_eq] at hq
  by_cases hs : s < M.length
  · have := Nat.eq_of_beq_eq_true (hc s hs)
    rw [Nat.zero_add] at this
    rw [← this, nland, Nat.testBit_and, testBit_mask n _ _ (by rw [rowsSn_eq]; omega)] at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  · rw [List.getD_eq_default _ _ (by omega), Nat.zero_testBit] at hq
    exact absurd hq (by decide)

theorem wf_bit' {n : Nat} {M : List Nat} (h : wfMatn n M = true) {s j t : Nat} (ht : t < 64)
    (hq : (M.getD s 0).testBit (64 * j + t) = true) : j < n ∧ 64 * s + t < n := by
  rw [← lget_eq] at hq
  have := (wf_bit h).2 s _ hq
  rw [rowsSn_eq] at this
  omega

theorem wfMat_eq (M : List Nat) : wfMat M = wfMatn 4370 M := rfl

@[expose] noncomputable def stripMatG (n : Nat) (S : List Nat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (lget S (i.val / 64)).testBit (64 * j.val + i.val % 64) then 1 else 0

theorem stripMat_eq (S : List Nat) : stripMat S = stripMatG 4370 S := rfl

theorem stripMatG_apply (n : Nat) (S : List Nat) (i j : Fin n) :
    stripMatG n S i j = bz ((S.getD (i.val / 64) 0).testBit (64 * j.val + i.val % 64)) := by
  rw [← lget_eq]
  rfl

theorem stripMatG_mul {n : Nat} (hn : n ≤ 4416) {A B : List Nat} (hA : A.length = 69)
    (hB : wfMatn n B = true) :
    stripMatG n A * stripMatG n B = stripMatG n (A.map (mulSn n B)) := by
  ext i j
  have hi : i.val / 64 < A.length := by omega
  rw [Matrix.mul_apply, stripMatG_apply, getD_map_of_lt hi,
    mulSn_bit n B _ j.val (i.val % 64) (Nat.mod_lt _ (by norm_num)), (wf_bit hB).1,
    decide_eq_true j.isLt, bz_true, mul_one]
  simp only [stripMatG_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k => bz (((A.getD (i.val / 64) 0).testBit (64 * k + i.val % 64)))
    * bz ((B.getD (k / 64) 0).testBit (64 * j.val + k % 64))) n]
  apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
  intro k _ hk
  rw [Finset.mem_range, Nat.not_lt] at hk
  cases hb : (B.getD (k / 64) 0).testBit (64 * j.val + k % 64)
  · rw [bz_false, mul_zero]
  · have := wf_bit' hB (Nat.mod_lt _ (by norm_num)) hb
    omega

theorem mulWn_nil (n A : Nat) : mulWn n [] A = A := rfl

theorem mulWn_cons (n : Nat) (B : List Nat) (Ws : List (List Nat)) (A : Nat) :
    mulWn n (B :: Ws) A = mulWn n Ws (mulSn n B A) := by
  change forceB (mulSn n B A) (mulWn n Ws) = _
  rw [forceB_eq']

theorem stripMatG_foldl {n : Nat} (hn : n ≤ 4416) : ∀ {Ws : List (List Nat)} {A : List Nat},
    (∀ W ∈ Ws, wfMatn n W = true) → A.length = 69 →
      (Ws.map (stripMatG n)).foldl (· * ·) (stripMatG n A) = stripMatG n (A.map (mulWn n Ws))
  | [], A, _, _ => by
    simp only [List.map_nil, List.foldl_nil]
    congr 1
    exact (List.map_id' A).symm
  | W :: Ws, A, hW, hA => by
    rw [List.map_cons, List.foldl_cons, stripMatG_mul hn hA (hW W List.mem_cons_self),
      stripMatG_foldl hn (fun W' h' => hW W' (List.mem_cons_of_mem _ h')) (by simpa using hA),
      List.map_map]
    congr 2
    funext a
    exact (mulWn_cons n W Ws a).symm

theorem natRecList_eq (f : Nat → Nat) : ∀ (m : Nat) (acc : List Nat),
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun k ih acc => ih (List.cons (f k) acc)) m acc = (List.range m).map f ++ acc
  | 0, acc => rfl
  | m + 1, acc => by
    change Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun k ih acc => ih (List.cons (f k) acc)) m (f m :: acc) = _
    rw [natRecList_eq f m, List.range_succ, List.map_append, List.append_assoc]
    rfl

theorem testBit_idSn (n s q : Nat) :
    (idSn n s).testBit q = (decide (q ≥ 4096 * s) &&
      (decide (q - 4096 * s < 65 * rowsSn n s) && decide ((q - 4096 * s) % 65 = 0))) := by
  unfold idSn
  rw [nshl, nmul, nmul, ndiv, nsub, nshl, Nat.one_shiftLeft, Nat.testBit_shiftLeft]
  change (decide (q ≥ 4096 * s) &&
    ((2 ^ (65 * rowsSn n s) - 1) / (2 ^ 65 - 1)).testBit (q - 4096 * s)) = _
  rw [← Nat.one_mul ((2 ^ (65 * rowsSn n s) - 1) / (2 ^ 65 - 1)),
    CFSG.KC.Benes.testBit_mul_div (by norm_num) rfl (by norm_num), testBit_one']

theorem stripMatG_id {n : Nat} (hn : n ≤ 4416) {L : List Nat}
    (hL : L = (List.range 69).map (idSn n)) : stripMatG n L = 1 := by
  ext i j
  rw [stripMatG_apply, Matrix.one_apply, hL]
  have hi : i.val / 64 < 69 := by omega
  rw [getD_map_of_lt (by simpa using hi), List.getD_eq_getElem?_getD, List.getElem?_range hi,
    Option.getD_some, testBit_idSn]
  have hr := rowsSn_eq n (i.val / 64)
  have hi' := i.isLt
  have hj' := j.isLt
  by_cases h : i = j
  · rw [ite_eq_left h]
    have h' : i.val = j.val := congrArg Fin.val h
    rw [← bz_true]
    congr 1
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [ite_eq_right h]
    have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
    rw [← bz_false]
    congr 1
    rw [Bool.eq_false_iff]
    simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem Q63_eq : Q63 = (2 ^ 3969 - 1) / (2 ^ 63 - 1) := by
  unfold Q63
  rw [ndiv, nsub, nshl, Nat.one_shiftLeft]
  change (2 ^ 3969 - 1) / 9223372036854775807 = _
  have e : (9223372036854775807 : Nat) = 2 ^ 63 - 1 := by norm_num
  rw [e]

theorem SM63_eq : SM63 = 1 * ((2 ^ 4032 - 1) / (2 ^ 64 - 1)) := by
  unfold SM63
  rw [ndiv, nsub, nshl, Nat.one_shiftLeft, Nat.one_mul, LM_eq]

@[expose] noncomputable def chunk (r q : Nat) : Nat :=
  Nat.shiftLeft (Nat.land (Nat.mul (Nat.land (Nat.shiftRight r (Nat.mul 63 q))
    9223372036854775807) Q63) SM63) (Nat.mul 4032 q)

theorem testBit_chunk (r q P : Nat) :
    (chunk r q).testBit P = (decide (4032 * q ≤ P) && (decide (P - 4032 * q < 3969) &&
      (decide ((P - 4032 * q) % 64 = 0) && r.testBit (63 * q + (P - 4032 * q) % 63)))) := by
  unfold chunk
  rw [nshl, nland, nmul, nmul, nland, nshr, nmul, Nat.testBit_shiftLeft, Nat.testBit_and]
  have e : (9223372036854775807 : Nat) = 2 ^ 63 - 1 := by norm_num
  change (decide (P ≥ 4032 * q) && ((((r >>> (63 * q)) &&& (2 ^ 63 - 1)) * Q63).testBit
    (P - 4032 * q) && SM63.testBit (P - 4032 * q))) = _
  rw [Q63_eq, CFSG.KC.Benes.testBit_mul_div (n := 63) (by norm_num) (by norm_num)
      (CFSG.KC.Benes.land_ones_lt _ _),
    SM63_eq, CFSG.KC.Benes.testBit_mul_div (n := 63) (by norm_num) (by norm_num) (by norm_num),
    testBit_one',
    Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  have h63 : (P - 4032 * q) % 63 < 63 := Nat.mod_lt _ (by norm_num)
  rw [decide_eq_true h63, Bool.and_true]
  by_cases h1 : 4032 * q ≤ P <;> by_cases h2 : P - 4032 * q < 3969 <;>
    by_cases h3 : (P - 4032 * q) % 64 = 0 <;> simp [h1, h2, h3]
  all_goals omega

theorem spreadRow_rec (r : Nat) : ∀ m P, (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q acc => Nat.lor acc (chunk r q)) m : Nat).testBit P = true ↔
      ∃ q < m, (chunk r q).testBit P = true
  | 0, P => by simp
  | m + 1, P => by
    change (Nat.lor _ (chunk r m)).testBit P = true ↔ _
    rw [nlor, Nat.testBit_or, Bool.or_eq_true, spreadRow_rec r m P]
    constructor
    · rintro (⟨q, hq, h⟩ | h)
      · exact ⟨q, by omega, h⟩
      · exact ⟨m, by omega, h⟩
    · rintro ⟨q, hq, h⟩
      by_cases hqm : q = m
      · subst hqm
        exact Or.inr h
      · exact Or.inl ⟨q, by omega, h⟩

theorem testBit_spreadRow {r : Nat} (hr : r < 2 ^ 4410) (P : Nat) :
    (spreadRow r).testBit P = (decide (P % 64 = 0) && r.testBit (P / 64)) := by
  have e := spreadRow_rec r 70 P
  change _ ↔ _ at e
  rw [Bool.eq_iff_iff]
  refine (e.trans ?_)
  simp only [testBit_chunk, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨q, _, h1, h2, h3, h4⟩
    have e2 : 63 * q + (P - 4032 * q) % 63 = P / 64 := by omega
    rw [e2] at h4
    exact ⟨by omega, h4⟩
  · rintro ⟨h1, h2⟩
    have hP : P / 64 < 4410 := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at h2
      exact absurd h2 (by decide)
    refine ⟨P / 64 / 63, by omega, by omega, by omega, by omega, ?_⟩
    have e2 : 63 * (P / 64 / 63) + (P - 4032 * (P / 64 / 63)) % 63 = P / 64 := by omega
    rw [e2]
    exact h2

theorem spreadRow_eq (r : Nat) : spreadRow r = Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun q acc => Nat.lor acc (chunk r q)) 70 := rfl

@[expose] noncomputable def sob (F n : Nat) (blk : List Nat) (t acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih t acc => Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft (nat_lit 1) F)
      (forceB (Nat.lor acc (Nat.shiftLeft (spreadRow (Nat.lor r (Nat.mul t (nat_lit 0)))) t))
        (fun acc' => ih (Nat.succ t) acc'))
      (Nat.beq (Nat.shiftRight r n) (nat_lit 0))) blk t acc

theorem stripOfBlock_eq (blk : List Nat) : stripOfBlock blk = sob 279680 4370 blk 0 0 := rfl

theorem stripOfBlockn_eq (n : Nat) (blk : List Nat) :
    stripOfBlockn n blk = sob 282624 n blk 0 0 := rfl

@[expose] noncomputable def orRows : List Nat → Nat → Nat
  | [], _ => 0
  | r :: rs, t => (spreadRow r <<< t) ||| orRows rs (t + 1)

theorem sob_spec (F n : Nat) : ∀ (blk : List Nat) (t acc : Nat),
    sob F n blk t acc = 2 ^ F ∨ ((∀ r ∈ blk, r < 2 ^ n) ∧ sob F n blk t acc = acc ||| orRows blk t)
  | [], t, acc => Or.inr ⟨by simp, by simp [sob, orRows]⟩
  | r :: blk, t, acc => by
    change Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 F)
      (forceB (Nat.lor acc (Nat.shiftLeft (spreadRow (Nat.lor r (Nat.mul t 0))) t))
        (fun acc' => sob F n blk (Nat.succ t) acc'))
      (Nat.beq (Nat.shiftRight r n) 0) = 2 ^ F ∨ ((∀ r' ∈ r :: blk, r' < 2 ^ n) ∧
        Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 F)
      (forceB (Nat.lor acc (Nat.shiftLeft (spreadRow (Nat.lor r (Nat.mul t 0))) t))
        (fun acc' => sob F n blk (Nat.succ t) acc'))
      (Nat.beq (Nat.shiftRight r n) 0) = acc ||| orRows (r :: blk) t)
    cases hb : Nat.beq (Nat.shiftRight r n) 0
    · left
      change Nat.shiftLeft 1 F = 2 ^ F
      rw [nshl, Nat.one_shiftLeft]
    · have hr : r < 2 ^ n := by
        have := Nat.eq_of_beq_eq_true hb
        rw [nshr, Nat.shiftRight_eq_div_pow] at this
        exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos n)).1 this
      change forceB _ (fun acc' => sob F n blk (Nat.succ t) acc') = 2 ^ F ∨
        ((∀ r' ∈ r :: blk, r' < 2 ^ n) ∧ forceB _ (fun acc' => sob F n blk (Nat.succ t) acc') = _)
      rw [forceB_eq']
      rcases sob_spec F n blk (Nat.succ t) _ with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨?_, ?_⟩
        · intro r' hr'
          rcases List.mem_cons.1 hr' with h' | h'
          · rw [h']
            exact hr
          · exact h1 r' h'
        · rw [h2, nlor, nmul, Nat.mul_zero, nlor, Nat.or_zero, nshl, orRows, Nat.or_assoc]

theorem testBit_orRows {j t' : Nat} (ht' : t' < 64) (hj : j < 4410) :
    ∀ (blk : List Nat) (t0 : Nat), (∀ r ∈ blk, r < 2 ^ 4410) → t0 + blk.length ≤ 64 →
      (orRows blk t0).testBit (64 * j + t') =
        (decide (t0 ≤ t' ∧ t' < t0 + blk.length) && (blk.getD (t' - t0) 0).testBit j)
  | [], t0, _, _ => by simp [orRows]
  | r :: blk, t0, hr, hl => by
    have hl' : t0 + blk.length + 1 ≤ 64 := by
      simp only [List.length_cons] at hl
      omega
    rw [orRows, Nat.testBit_or, Nat.testBit_shiftLeft,
      testBit_orRows ht' hj blk (t0 + 1) (fun r' h' => hr r' (List.mem_cons_of_mem _ h'))
        (by omega),
      testBit_spreadRow (hr r List.mem_cons_self)]
    simp only [List.length_cons]
    by_cases h1 : t' = t0
    · subst h1
      have e1 : (64 * j + t' - t') / 64 = j := by omega
      rw [e1]
      simp
    · by_cases h2 : t0 + 1 ≤ t' ∧ t' < t0 + 1 + blk.length
      · have e1 : t' - t0 = (t' - (t0 + 1)) + 1 := by omega
        rw [e1, List.getD_cons_succ, decide_eq_true h2]
        have h3 : ¬ ((64 * j + t' - t0) % 64 = 0) := by omega
        simp [h3]
        omega
      · rw [decide_eq_false h2]
        have h3 : ¬ (t0 ≤ t' ∧ t' < t0 + (blk.length + 1)) := by omega
        rw [decide_eq_false h3]
        by_cases h4 : 64 * j + t' ≥ t0
        · have h5 : ¬ ((64 * j + t' - t0) % 64 = 0) := by omega
          simp [h5]
        · simp [h4]

theorem sob_strip {F n : Nat} (hF : 64 * n ≤ F) (hn : n ≤ 4410) {blk : List Nat} {T : Nat}
    (hlen : blk.length ≤ 64) (h : sob F n blk 0 0 = T) (hT : ∀ q, T.testBit q = true → q < 64 * n) :
    (∀ r ∈ blk, r < 2 ^ n) ∧ ∀ j t, t < 64 →
      T.testBit (64 * j + t) = (decide (t < blk.length) && (blk.getD t 0).testBit j) := by
  rcases sob_spec F n blk 0 0 with h1 | ⟨h1, h2⟩
  · have := hT F (by rw [← h, h1, Nat.testBit_two_pow_self])
    omega
  · refine ⟨h1, ?_⟩
    intro j t ht
    have h4410 : ∀ r ∈ blk, r < 2 ^ 4410 := fun r hr =>
      Nat.lt_of_lt_of_le (h1 r hr) (Nat.pow_le_pow_right (by norm_num) hn)
    rw [← h, h2, Nat.zero_or]
    by_cases hj : j < 4410
    · rw [testBit_orRows ht hj blk 0 h4410 (by omega), Nat.sub_zero]
      simp
    · have e1 : (blk.getD t 0).testBit j = false := by
        rw [List.getD_eq_getElem?_getD]
        cases hx : blk[t]? with
        | none => simp
        | some x =>
          have hx' := List.mem_of_getElem? hx
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (h4410 x hx')
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [e1, Bool.and_false]
      cases hb : (orRows blk 0).testBit (64 * j + t)
      · rfl
      · have := hT (64 * j + t) (by rw [← h, h2, Nat.zero_or]; exact hb)
        omega

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem rows_of_blocks {F n : Nat} (hF : 64 * n ≤ F) (hn : n ≤ 4410) {R : List (List Nat)}
    {S : List Nat} (hS : wfMatn n S = true)
    (hR : ∀ s < 69, (R.getD s []).length = rowsSn n s ∧ sob F n (R.getD s []) 0 0 = S.getD s 0)
    {i : Nat} (hi : i < n) :
    (R.getD (i / 64) []).getD (i % 64) 0 < 2 ^ n ∧ ∀ j,
      ((R.getD (i / 64) []).getD (i % 64) 0).testBit j = (S.getD (i / 64) 0).testBit (64 * j + i % 64) := by
  obtain ⟨hl, hb⟩ := hR (i / 64) (by omega)
  have hrs := rowsSn_eq n (i / 64)
  have ht : i % 64 < (R.getD (i / 64) []).length := by omega
  have hT : ∀ q, (S.getD (i / 64) 0).testBit q = true → q < 64 * n := by
    intro q hq
    rw [← lget_eq] at hq
    exact ((wf_bit hS).2 _ q hq).1
  obtain ⟨h1, h2⟩ := sob_strip hF hn (by omega) hb hT
  refine ⟨h1 _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht), ?_⟩
  intro j
  rw [h2 j _ (Nat.mod_lt _ (by norm_num)), decide_eq_true ht, Bool.true_and]

theorem allBlocks_spec : ∀ {R : List (List Nat)} {S : List Nat} {s0 : Nat}, AllBlocks R S s0 →
    R.length = S.length ∧ ∀ i < R.length, blockOK (R.getD i []) (S.getD i 0) (s0 + i) = true
  | _, _, _, .nil _ => ⟨rfl, fun i hi => absurd hi (by simp)⟩
  | _, _, _, .cons blk T s R S hb h => by
    obtain ⟨h1, h2⟩ := allBlocks_spec h
    refine ⟨by simp [h1], ?_⟩
    intro i hi
    cases i with
    | zero => simpa using hb
    | succ i =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      have := h2 i (by simp at hi; omega)
      rwa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 i] at this

theorem blockOK_spec {blk : List Nat} {T s : Nat} (h : blockOK blk T s = true) :
    blk.length = rowsSn 4370 s ∧ sob 279680 4370 blk 0 0 = T := by
  unfold blockOK at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact ⟨by rw [← lenL_eq]; exact Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

@[expose] def VL : List Nat → Nat → Nat → Nat
  | [], _, acc => acc
  | r :: L, v, acc => VL L (v >>> 1) (acc ^^^ (v &&& 1) * r)

@[expose] noncomputable def vInner (ih : Nat → Nat → Nat) (blk : List Nat) (v acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun v acc => ih v acc)
    (fun r _ ih2 v acc =>
      forceB (Nat.xor acc (Nat.mul (Nat.land v (nat_lit 1)) r)) (fun acc' =>
        ih2 (Nat.shiftRight v (nat_lit 1)) acc')) blk v acc

@[expose] noncomputable def vOuter (Rb : List (List Nat)) (v acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun blk _ ih v acc => vInner ih blk v acc) Rb v acc

theorem vecMul_eq_vOuter (Rb : List (List Nat)) (v : Nat) : vecMul Rb v = vOuter Rb v 0 := rfl

theorem vInner_eq (ih : Nat → Nat → Nat) : ∀ (blk : List Nat) (v acc : Nat),
    vInner ih blk v acc = ih (v >>> blk.length) (VL blk v acc)
  | [], v, acc => rfl
  | r :: blk, v, acc => by
    change forceB _ (fun acc' => vInner ih blk (Nat.shiftRight v 1) acc') = _
    rw [forceB_eq', vInner_eq ih blk, List.length_cons, VL, nshr, nxor, nmul, nland,
      ← Nat.shiftRight_add, Nat.add_comm 1]

theorem VL_append : ∀ (L1 L2 : List Nat) (v acc : Nat),
    VL (L1 ++ L2) v acc = VL L2 (v >>> L1.length) (VL L1 v acc)
  | [], L2, v, acc => rfl
  | r :: L1, L2, v, acc => by
    rw [List.cons_append, VL, VL, VL_append L1 L2, List.length_cons, ← Nat.shiftRight_add,
      Nat.add_comm 1]

theorem vOuter_eq : ∀ (Rb : List (List Nat)) (v acc : Nat), vOuter Rb v acc = VL Rb.flatten v acc
  | [], v, acc => rfl
  | blk :: Rb, v, acc => by
    change vInner (vOuter Rb) blk v acc = _
    rw [vInner_eq, vOuter_eq Rb, List.flatten_cons, VL_append]

theorem testBit_and_one_mul (v r j : Nat) :
    ((v &&& 1) * r).testBit j = (v.testBit 0 && r.testBit j) := by
  rw [Nat.and_one_is_mod, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one v with h | h <;> simp [h]

theorem VL_bit (j : Nat) : ∀ (L : List Nat) (v acc : Nat),
    bz ((VL L v acc).testBit j) = bz (acc.testBit j) +
      ∑ m ∈ Finset.range L.length, bz (v.testBit m) * bz ((L.getD m 0).testBit j)
  | [], v, acc => by simp [VL]
  | r :: L, v, acc => by
    rw [VL, VL_bit j L, Nat.testBit_xor, bz_xor, testBit_and_one_mul, bz_and, List.length_cons,
      Finset.sum_range_succ']
    simp only [Nat.testBit_shiftRight, List.getD_cons_succ, List.getD_cons_zero]
    have e : ∀ m, 1 + m = m + 1 := fun m => Nat.add_comm 1 m
    simp only [e]
    ring

theorem VL_lt {N : Nat} : ∀ (L : List Nat), (∀ r ∈ L, r < 2 ^ N) → ∀ v acc, acc < 2 ^ N →
    VL L v acc < 2 ^ N
  | [], _, v, acc, h => h
  | r :: L, hL, v, acc, h => by
    rw [VL]
    apply VL_lt L (fun r' h' => hL r' (List.mem_cons_of_mem _ h'))
    apply Nat.xor_lt_two_pow h
    rw [Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one v with h' | h' <;> rw [h']
    · simp
    · simpa using hL r List.mem_cons_self

theorem flatten_getD : ∀ (Rb : List (List Nat)),
    (∀ s, s + 1 < Rb.length → (Rb.getD s []).length = 64) →
    (∀ s < Rb.length, (Rb.getD s []).length ≤ 64) →
    ∀ i, Rb.flatten.getD i 0 = (Rb.getD (i / 64) []).getD (i % 64) 0
  | [], _, _, i => by simp
  | [b], _, h2, i => by
    have hb := h2 0 (by simp)
    simp only [List.getD_cons_zero] at hb
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    by_cases hi : i < 64
    · rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, List.getD_cons_zero]
    · rw [List.getD_eq_default _ _ (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, i / 64 = k + 1 := ⟨i / 64 - 1, by omega⟩
      rw [hk, List.getD_cons_succ]
      simp
  | b :: b' :: Rb, h1, h2, i => by
    have hb := h1 0 (by simp)
    simp only [List.getD_cons_zero] at hb
    rw [List.flatten_cons]
    by_cases hi : i < 64
    · rw [List.getD_append _ _ _ _ (by omega), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi,
        List.getD_cons_zero]
    · rw [List.getD_append_right _ _ _ _ (by omega), hb,
        flatten_getD (b' :: Rb) (fun s hs => by
          have := h1 (s + 1) (by simp at hs ⊢; omega)
          rwa [List.getD_cons_succ] at this)
          (fun s hs => by
            have := h2 (s + 1) (by simp at hs ⊢; omega)
            rwa [List.getD_cons_succ] at this)]
      obtain ⟨k, hk⟩ : ∃ k, i / 64 = k + 1 := ⟨i / 64 - 1, by omega⟩
      have e1 : (i - 64) / 64 = k := by omega
      have e2 : (i - 64) % 64 = i % 64 := by omega
      rw [hk, List.getD_cons_succ, e1, e2]

theorem eqL_eq : ∀ (a b : List Nat), eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by unfold eqL; simp)
  | _ :: _, [], h => absurd h (by unfold eqL; simp)
  | x :: a, y :: b, h => by
    change andB (Nat.beq x y) (eqL a b) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqL_eq a b h.2]

theorem xorL_spec : ∀ (a b : List Nat), a.length = b.length →
    (xorL a b).length = a.length ∧ ∀ t, (xorL a b).getD t 0 = a.getD t 0 ^^^ b.getD t 0
  | [], [], _ => ⟨rfl, fun t => by simp [xorL]⟩
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)
  | x :: a, y :: b, h => by
    change (Nat.xor x y :: xorL a b).length = _ ∧ ∀ t, (Nat.xor x y :: xorL a b).getD t 0 = _
    obtain ⟨h1, h2⟩ := xorL_spec a b (by simpa using h)
    refine ⟨by simp [h1], ?_⟩
    intro t
    cases t with
    | zero => rfl
    | succ t => rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, h2]

theorem zeros_eq : ∀ m : Nat, (Nat.rec (motive := fun _ => List Nat) List.nil
    (fun _ acc => List.cons (nat_lit 0) acc) m : List Nat) = List.replicate m 0
  | 0 => rfl
  | m + 1 => by
    change 0 :: (Nat.rec (motive := fun _ => List Nat) List.nil
      (fun _ acc => List.cons (nat_lit 0) acc) m : List Nat) = _
    rw [zeros_eq m, List.replicate_succ]

theorem xorBlocks_spec (m j : Nat) : ∀ (Bs : List (List Nat)), (∀ B ∈ Bs, B.length = m) →
    (xorBlocks m Bs).length = m ∧ ∀ t,
      bz (((xorBlocks m Bs).getD t 0).testBit j) = (Bs.map fun B => bz ((B.getD t 0).testBit j)).sum
  | [], _ => by
    have e : xorBlocks m [] = List.replicate m 0 := zeros_eq m
    rw [e]
    refine ⟨by simp, fun t => ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp
  | B :: Bs, h => by
    change (xorL B (xorBlocks m Bs)).length = m ∧ ∀ t,
      bz (((xorL B (xorBlocks m Bs)).getD t 0).testBit j) = _
    obtain ⟨h1, h2⟩ := xorBlocks_spec m j Bs (fun B' h' => h B' (List.mem_cons_of_mem _ h'))
    have hB := h B List.mem_cons_self
    obtain ⟨h3, h4⟩ := xorL_spec B (xorBlocks m Bs) (by rw [hB, h1])
    refine ⟨by rw [h3, hB], fun t => ?_⟩
    rw [h4, Nat.testBit_xor, bz_xor, h2, List.map_cons, List.sum_cons]

@[expose] noncomputable def fInner (S : Nat) (f : Nat → Nat → Nat → Nat) (ih : Nat → Nat → Nat)
    (m T i st : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ i st => ih i st)
    (fun _ ih2 T i st =>
      forceB (f i (Nat.land T S) st) (fun st' => ih2 (Nat.shiftRight T (nat_lit 1)) (Nat.succ i) st'))
    m T i st

@[expose] noncomputable def fOuter (S : Nat) (f : Nat → Nat → Nat → Nat) (M : List Nat)
    (i st : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ st => st)
    (fun T _ ih i st => fInner S f ih (nat_lit 64) T i st) M i st

theorem foldRows_eq (f : Nat → Nat → Nat → Nat) (M : List Nat) (st : Nat) :
    foldRows f M st = fOuter SM f M 0 st := rfl

theorem foldRowsn_eq (n : Nat) (f : Nat → Nat → Nat → Nat) (M : List Nat) (st : Nat) :
    foldRowsn n f M st = fOuter (SMn n) f M 0 st := rfl

theorem foldl_ext {f g : Nat → Nat → Nat} : ∀ (l : List Nat) (st : Nat),
    (∀ x ∈ l, ∀ st, f st x = g st x) → l.foldl f st = l.foldl g st
  | [], _, _ => rfl
  | x :: l, st, h => by
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self,
      foldl_ext l _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem fInner_eq (S : Nat) (f : Nat → Nat → Nat → Nat) (ih : Nat → Nat → Nat) : ∀ (m T i st : Nat),
    fInner S f ih m T i st =
      ih (i + m) ((List.range m).foldl (fun st x => f (i + x) ((T >>> x) &&& S) st) st)
  | 0, T, i, st => rfl
  | m + 1, T, i, st => by
    change forceB (f i (Nat.land T S) st)
      (fun st' => fInner S f ih m (Nat.shiftRight T 1) (Nat.succ i) st') = _
    rw [forceB_eq', fInner_eq S f ih m, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have e1 : Nat.succ i + m = i + (m + 1) := by omega
    rw [e1, Nat.add_zero, Nat.shiftRight_zero, nland, nshr]
    congr 1
    apply foldl_ext
    intro x _ st'
    rw [← Nat.shiftRight_add]
    have e2 : Nat.succ i + x = i + Nat.succ x := by omega
    have e3 : 1 + x = Nat.succ x := by omega
    rw [e2, e3]

theorem fOuter_eq (S : Nat) (f : Nat → Nat → Nat → Nat) : ∀ (M : List Nat) (i st : Nat),
    fOuter S f M i st = (List.range (64 * M.length)).foldl
      (fun st x => f (i + x) (((M.getD (x / 64) 0) >>> (x % 64)) &&& S) st) st
  | [], i, st => rfl
  | T :: M, i, st => by
    change fInner S f (fOuter S f M) 64 T i st = _
    rw [fInner_eq, fOuter_eq S f M, List.length_cons, Nat.mul_succ, Nat.add_comm (64 * M.length),
      List.range_add, List.foldl_append, List.foldl_map]
    congr 1
    · funext st' x
      have e1 : (64 + x) / 64 = x / 64 + 1 := by omega
      have e2 : (64 + x) % 64 = x % 64 := by omega
      rw [e1, e2, List.getD_cons_succ, Nat.add_assoc]

theorem bool_rec_eq {α : Sort _} (x y : α) (b : Bool) :
    (Bool.rec (motive := fun _ => α) x y b) = if b then y else x := by
  cases b <;> rfl

theorem log2_lt_of {r st : Nat} (h0 : r ≠ 0) (h1 : r < st) (h2 : r < r ^^^ st) :
    r.log2 < st.log2 := by
  have hst : st ≠ 0 := by omega
  have hlt := @Nat.lt_log2_self st
  have htop := Nat.testBit_log2 hst
  have hr' : r < 2 ^ (st.log2 + 1) := by omega
  have hhi : ∀ x, x < 2 ^ (st.log2 + 1) → ∀ i, st.log2 < i → x.testBit i = false := fun x hx i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
  have hb : r.testBit st.log2 = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hx : r ^^^ st < 2 ^ st.log2 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [Nat.testBit_xor]
      by_cases hi' : i = st.log2
      · rw [hi', hc, htop]
        rfl
      · rw [hhi r hr' i (by omega), hhi st hlt i (by omega)]
        rfl
    have := Nat.ge_two_pow_of_testBit hc
    omega
  have hr2 : r < 2 ^ st.log2 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hi' : i = st.log2
    · rw [hi', hb]
    · exact hhi r hr' i (by omega)
  exact (Nat.log2_lt h0).2 hr2

theorem echStep_zero (r : Nat) : echStep r 0 = 0 := by
  unfold echStep
  rw [andB_eq, andB_eq]
  have : Nat.blt r 0 = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
    omega
  rw [this]
  simp

theorem echStep_spec {r st : Nat} (h : echStep r st ≠ 0) :
    echStep r st = r ∧ r ≠ 0 ∧ r.log2 < st.log2 := by
  unfold echStep at h ⊢
  rw [andB_eq, andB_eq] at h ⊢
  cases hc : (notB (Nat.beq r 0) && (Nat.blt r st && Nat.blt r (Nat.xor r st)))
  · rw [hc] at h
    exact absurd rfl h
  · simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    obtain ⟨h1, h2, h3⟩ := hc
    have h0 : r ≠ 0 := by
      intro e
      rw [e] at h1
      exact absurd h1 (by decide)
    exact ⟨rfl, h0, log2_lt_of h0 h2 h3⟩

theorem ech_fold (act : Nat → Bool) (pass : Nat → Nat → Bool) (row : Nat → Nat) (st0 : Nat) :
    ∀ N, (List.range N).foldl (fun st i => if act i then echStep (row i) st
        else if pass i (row i) then st else 0) st0 ≠ 0 →
      (∀ i < N, act i = true → row i ≠ 0) ∧ (∀ i < N, act i = false → pass i (row i) = true) ∧
      (∀ i i', i < i' → i' < N → act i = true → act i' = true → (row i').log2 < (row i).log2) ∧
      (∀ i < N, act i = true → ((List.range N).foldl (fun st i => if act i then echStep (row i) st
        else if pass i (row i) then st else 0) st0).log2 ≤ (row i).log2)
  | 0, _ => ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      fun _ _ _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  | N + 1, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    generalize hF : (List.range N).foldl (fun st i => if act i then echStep (row i) st
        else if pass i (row i) then st else 0) st0 = F at h ⊢
    have hF0 : F ≠ 0 := by
      intro e
      rw [e] at h
      apply h
      cases act N
      · simp
      · simp [echStep_zero]
    obtain ⟨A, B, C, D⟩ := ech_fold act pass row st0 N (by rw [hF]; exact hF0)
    rw [hF] at D
    cases ha : act N
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hp : pass N (row N)
      · rw [hp] at h
        exact absurd rfl h
      · simp only [↓reduceIte]
        refine ⟨fun i hi hai => ?_, fun i hi hai => ?_, fun i i' hii hi' ha1 ha2 => ?_,
          fun i hi hai => ?_⟩
        · by_cases e : i = N
          · rw [e, ha] at hai
            exact absurd hai (by decide)
          · exact A i (by omega) hai
        · by_cases e : i = N
          · rw [e]
            exact hp
          · exact B i (by omega) hai
        · by_cases e : i' = N
          · rw [e, ha] at ha2
            exact absurd ha2 (by decide)
          · exact C i i' hii (by omega) ha1 ha2
        · by_cases e : i = N
          · rw [e, ha] at hai
            exact absurd hai (by decide)
          · exact D i (by omega) hai
    · simp only [ha, ↓reduceIte] at h ⊢
      obtain ⟨e1, e2, e3⟩ := echStep_spec h
      rw [e1]
      refine ⟨fun i hi hai => ?_, fun i hi hai => ?_, fun i i' hii hi' ha1 ha2 => ?_,
        fun i hi hai => ?_⟩
      · by_cases e : i = N
        · rw [e]
          exact e2
        · exact A i (by omega) hai
      · by_cases e : i = N
        · rw [e, ha] at hai
          exact absurd hai (by decide)
        · exact B i (by omega) hai
      · by_cases e : i' = N
        · rw [e]
          have := D i (by omega) ha1
          omega
        · exact C i i' hii (by omega) ha1 ha2
      · by_cases e : i = N
        · rw [e]
        · have := D i (by omega) hai
          omega

theorem lead_aux {ι : Type*} {m : Nat} (v : ι → Fin m → ZMod 2) (c : ι → Fin m)
    (h1 : ∀ i, v i (c i) = 1) (h2 : ∀ i j, c i < j → v i j = 0) (hc : Function.Injective c)
    (s : Finset ι) (g : ι → ZMod 2) (hg : ∀ j, ∑ x ∈ s, g x * v x j = 0) (i : ι) (hi : i ∈ s) :
    g i = 0 := by
  classical
  by_contra hne
  have hne' : (s.filter (fun x => g x ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hne⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image _ c hne'
  have hi0' := Finset.mem_filter.1 hi0
  have e := hg (c i0)
  rw [Finset.sum_eq_single i0] at e
  · rw [h1, mul_one] at e
    exact hi0'.2 e
  · intro b hb hb0
    by_cases hg0 : g b = 0
    · rw [hg0, zero_mul]
    · have hle := hmax b (Finset.mem_filter.2 ⟨hb, hg0⟩)
      have hne2 : c b ≠ c i0 := fun e => hb0 (hc e)
      rw [h2 b (c i0) (lt_of_le_of_ne hle hne2), mul_zero]
  · intro h
    exact absurd hi0'.1 h

theorem linIndep_of_lead {ι : Type*} {m : Nat} (v : ι → Fin m → ZMod 2) (c : ι → Fin m)
    (h1 : ∀ i, v i (c i) = 1) (h2 : ∀ i j, c i < j → v i j = 0) (hc : Function.Injective c) :
    LinearIndependent (ZMod 2) v := by
  rw [linearIndependent_iff'ₛ]
  intro s f f' hff i hi
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  apply key
  refine lead_aux v c h1 h2 hc s (fun x => f x + f' x) (fun j => ?_) i hi
  have e1 := congrFun hff j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1
  have two : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [Finset.sum_congr rfl (fun x _ => add_mul (f x) (f' x) (v x j)), Finset.sum_add_distrib, e1,
    two]

@[expose] noncomputable def rowAt (S : Nat) (M : List Nat) (x : Nat) : Nat :=
  ((M.getD (x / 64) 0) >>> (x % 64)) &&& S

theorem testBit_rowAt (n : Nat) (M : List Nat) (x j : Nat) :
    (rowAt (SMn n) M x).testBit (64 * j) =
      ((M.getD (x / 64) 0).testBit (64 * j + x % 64) && decide (j < n)) := by
  rw [rowAt, Nat.testBit_and, Nat.testBit_shiftRight, testBit_SMn_mul, Nat.add_comm (x % 64)]

theorem stripMatG_linIndep {n : Nat} {M : List Nat} {ι : Type*} (r : ι → Fin n)
    (hne : ∀ i, rowAt (SMn n) M (r i).val ≠ 0)
    (hinj : ∀ i i', (rowAt (SMn n) M (r i).val).log2 = (rowAt (SMn n) M (r i').val).log2 → i = i') :
    LinearIndependent (ZMod 2) (fun i => stripMatG n M (r i)) := by
  have hb : ∀ x q, (rowAt (SMn n) M x).testBit q = true → q % 64 = 0 ∧ q < 64 * n := by
    intro x q hq
    rw [rowAt, Nat.testBit_and, testBit_SMn] at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    exact ⟨hq.2.2, hq.2.1⟩
  have hlog : ∀ i, (rowAt (SMn n) M (r i).val).log2 % 64 = 0 ∧
      (rowAt (SMn n) M (r i).val).log2 < 64 * n := fun i => hb _ _ (Nat.testBit_log2 (hne i))
  let c : ι → Fin n := fun i => ⟨(rowAt (SMn n) M (r i).val).log2 / 64, by
    have := hlog i
    omega⟩
  have hv : (fun i => stripMatG n M (r i)) =
      fun i j => bz ((rowAt (SMn n) M (r i).val).testBit (64 * j.val)) := by
    funext i j
    rw [stripMatG_apply, testBit_rowAt, decide_eq_true j.isLt, Bool.and_true]
  rw [hv]
  apply linIndep_of_lead _ c
  · intro i
    have h1 := hlog i
    have e : 64 * (c i).val = (rowAt (SMn n) M (r i).val).log2 := by
      change 64 * ((rowAt (SMn n) M (r i).val).log2 / 64) = _
      omega
    rw [e, Nat.testBit_log2 (hne i), bz_true]
  · intro i j hij
    have hij' : (c i).val < j.val := hij
    change (rowAt (SMn n) M (r i).val).log2 / 64 < j.val at hij'
    have h1 := hlog i
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (@Nat.lt_log2_self _)
      (Nat.pow_le_pow_right (by norm_num) (by omega))), bz_false]
  · intro i i' e
    apply hinj
    have e' : (rowAt (SMn n) M (r i).val).log2 / 64 = (rowAt (SMn n) M (r i').val).log2 / 64 :=
      congrArg Fin.val e
    have h1 := hlog i
    have h2 := hlog i'
    omega

theorem mulS_eq (Bs : List Nat) (A : Nat) : mulS Bs A = mulSn 4370 Bs A := rfl

theorem mulW_eq (Ws : List (List Nat)) (A : Nat) : mulW Ws A = mulWn 4370 Ws A := rfl

theorem idS_eq (s : Nat) : idS s = idSn 4370 s := rfl

theorem idStrips_eq : idStrips = (List.range 69).map (idSn 4370) := by
  unfold idStrips
  refine (natRecList_eq idS 69 []).trans ?_
  rw [List.append_nil]
  exact congrArg (List.map · _) (funext idS_eq)

theorem idStripsG_eq (n : Nat) : (Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun k ih acc => ih (List.cons (idSn n k) acc)) (nat_lit 69) List.nil : List Nat) =
      (List.range 69).map (idSn n) := by
  refine (natRecList_eq (idSn n) 69 []).trans ?_
  rw [List.append_nil]

theorem allStrips_spec {Ws : List (List Nat)} : ∀ {A C : List Nat}, AllStrips Ws A C →
    C = A.map (mulWn 4370 Ws)
  | _, _, .nil => rfl
  | _, _, .cons a c as cs hb h => by
    rw [allStrips_spec h, List.map_cons, ← Nat.eq_of_beq_eq_true hb]
    rfl

@[expose] def StripShape (n : Nat) (X : List Nat) : Prop :=
  X.length = 69 ∧ ∀ s j t, t < 64 → (X.getD s 0).testBit (64 * j + t) = true → j < n ∧ 64 * s + t < n

theorem stripShape_of_wf {n : Nat} {X : List Nat} (h : wfMatn n X = true) : StripShape n X :=
  ⟨(wf_bit h).1, fun _ _ _ ht hq => wf_bit' h ht hq⟩

theorem stripShape_id (n : Nat) : StripShape n ((List.range 69).map (idSn n)) := by
  refine ⟨by simp, ?_⟩
  intro s j t ht hq
  by_cases hs : s < 69
  · rw [getD_map_of_lt (by simpa using hs), List.getD_eq_getElem?_getD, List.getElem?_range hs,
      Option.getD_some, testBit_idSn] at hq
    have hr := rowsSn_eq n s
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    omega
  · rw [List.getD_eq_default _ _ (by simp; omega), Nat.zero_testBit] at hq
    exact absurd hq (by decide)

theorem stripMatG_inj {n : Nat} {X Y : List Nat} (hX : StripShape n X) (hY : StripShape n Y)
    (h : stripMatG n X = stripMatG n Y) : X = Y := by
  have hs : ∀ s < 69, X.getD s 0 = Y.getD s 0 := by
    intro s _
    apply Nat.eq_of_testBit_eq
    intro q
    have hq : q = 64 * (q / 64) + q % 64 := by omega
    have ht : q % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have key : ∀ (hj : q / 64 < n) (hi : 64 * s + q % 64 < n),
        (X.getD s 0).testBit q = (Y.getD s 0).testBit q := by
      intro hj hi
      have e := congrFun (congrFun h ⟨64 * s + q % 64, hi⟩) ⟨q / 64, hj⟩
      rw [stripMatG_apply, stripMatG_apply] at e
      have e1 : (64 * s + q % 64) / 64 = s := by omega
      have e2 : (64 * s + q % 64) % 64 = q % 64 := by omega
      simp only [e1, e2] at e
      rw [← hq] at e
      exact bz_inj e
    cases hx : (X.getD s 0).testBit q
    · cases hy : (Y.getD s 0).testBit q
      · rfl
      · rw [hq] at hy
        obtain ⟨hj, hi⟩ := hY.2 s _ _ ht hy
        rw [← hq] at hy
        rw [← hx, ← hy]
        exact key hj hi
    · rw [hq] at hx
      obtain ⟨hj, hi⟩ := hX.2 s _ _ ht hx
      rw [← hq] at hx
      rw [← hx]
      exact key hj hi
  apply List.ext_getElem (by rw [hX.1, hY.1])
  intro s h1 h2
  have := hs s (by rw [hX.1] at h1; exact h1)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem wfFold_of (chk : Nat → Nat → Bool) : ∀ (M : List Nat) (s : Nat),
    (∀ i < M.length, chk (M.getD i 0) (s + i) = true) → wfFold chk M s = s + M.length
  | [], s, _ => rfl
  | T :: M, s, h => by
    change Bool.rec (motive := fun _ => Nat) 100000 (wfFold chk M (Nat.succ s)) (chk T s) = _
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    rw [h0]
    change wfFold chk M (s + 1) = _
    rw [wfFold_of chk M (s + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      have e : s + (i + 1) = s + 1 + i := by omega
      rwa [List.getD_cons_succ, e] at this), List.length_cons]
    omega

theorem isId_id : isId ((List.range 69).map (idSn 4370)) = true := by
  change Nat.beq (wfFold (fun T s => Nat.beq T (idS s)) ((List.range 69).map (idSn 4370)) 0) 69 = true
  rw [wfFold_of _ _ 0 (fun i hi => by
    rw [List.length_map, List.length_range] at hi
    rw [getD_map_of_lt (by simpa using hi), List.getD_eq_getElem?_getD, List.getElem?_range hi,
      Option.getD_some, Nat.zero_add, idS_eq]
    exact Nat.beq_refl _)]
  simp

end CFSG.KC.BM.SL

end
