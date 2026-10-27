module

public import Certificates.Data.Kernel.Misc.Ree
public import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KC.Misc.Ree

open Polynomial

@[expose] noncomputable def decL (x : ℕ) : (ZMod 3)[X] :=
  ∑ i ∈ Finset.range x, C ((x / 2 ^ (32 * i) % 2 ^ 32 : ℕ) : ZMod 3) * X ^ i

noncomputable def mkP (c : ℕ → ℕ) (n : ℕ) : ℕ[X] := ∑ i ∈ Finset.range n, monomial i (c i)

theorem coeff_mkP (c : ℕ → ℕ) (n i : ℕ) : (mkP c n).coeff i = if i < n then c i else 0 := by
  simp [mkP, finsetSum_coeff, coeff_monomial]

theorem eval_mkP (c : ℕ → ℕ) (n x : ℕ) :
    (mkP c n).eval x = ∑ i ∈ Finset.range n, c i * x ^ i := by
  simp [mkP, eval_finsetSum, eval_monomial]

def Bd (p : ℕ[X]) (B n : ℕ) : Prop := (∀ i, p.coeff i ≤ B) ∧ ∀ i, n ≤ i → p.coeff i = 0

theorem eq_mkP {p : ℕ[X]} {B n : ℕ} (h : Bd p B n) : p = mkP p.coeff n := by
  ext i
  rw [coeff_mkP]
  split_ifs with hi
  · rfl
  · exact h.2 i (by omega)

def lane (x i : ℕ) : ℕ := x / 2 ^ (32 * i) % 2 ^ 32

theorem lane_lt (x i : ℕ) : lane x i < 2 ^ 32 := Nat.mod_lt _ (by norm_num)

theorem eval_divX (p : ℕ[X]) :
    p.eval (2 ^ 32) = p.coeff 0 + 2 ^ 32 * (divX p).eval (2 ^ 32) := by
  conv_lhs => rw [← divX_mul_X_add p]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  ring

theorem lane_eval {p : ℕ[X]} (hp : ∀ i, p.coeff i < 2 ^ 32) (i : ℕ) :
    lane (p.eval (2 ^ 32)) i = p.coeff i := by
  induction i generalizing p with
  | zero =>
    rw [lane, eval_divX, Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hp 0)]
  | succ i ih =>
    have h1 : ∀ j, (divX p).coeff j < 2 ^ 32 := fun j => by rw [coeff_divX]; exact hp _
    rw [← coeff_divX, ← ih h1, lane, lane, eval_divX, Nat.mul_succ, pow_add,
      mul_comm (2 ^ (32 * i)), ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt (hp 0), Nat.zero_add]

theorem testBit_lane (x i t : ℕ) (ht : t < 32) :
    (lane x i).testBit t = x.testBit (t + 32 * i) := by
  rw [lane, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [ht]

theorem eq_of_testBit_lt {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : ∀ t < 32, a.testBit t = b.testBit t) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 32
  · exact h t ht
  · have hle : 2 ^ 32 ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle), Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hb hle)]

theorem lane_ext {x y : ℕ} (h : ∀ i, lane x i = lane y i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hj : j = j % 32 + 32 * (j / 32) := by omega
  rw [hj, ← testBit_lane x _ _ (Nat.mod_lt _ (by norm_num)),
    ← testBit_lane y _ _ (Nat.mod_lt _ (by norm_num)), h]

theorem lane_and (x y i : ℕ) : lane (x &&& y) i = lane x i &&& lane y i := by
  apply eq_of_testBit_lt (lane_lt _ _) (Nat.and_lt_two_pow _ (lane_lt _ _))
  intro t ht
  rw [testBit_lane _ _ _ ht, Nat.testBit_and, Nat.testBit_and, testBit_lane _ _ _ ht,
    testBit_lane _ _ _ ht]

theorem lane_mod {x i k : ℕ} (h : i < k) : lane (x % 2 ^ (32 * k)) i = lane x i := by
  apply eq_of_testBit_lt (lane_lt _ _) (lane_lt _ _)
  intro t ht
  rw [testBit_lane _ _ _ ht, testBit_lane _ _ _ ht, Nat.testBit_mod_two_pow]
  have : t + 32 * i < 32 * k := by omega
  simp [this]

theorem lane_of_le {x i k : ℕ} (hx : x < 2 ^ (32 * k)) (h : k ≤ i) : lane x i = 0 := by
  rw [lane, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))),
    Nat.zero_mod]

theorem eval_lt {c : ℕ → ℕ} (hc : ∀ i, c i < 2 ^ 32) (n : ℕ) :
    (mkP c n).eval (2 ^ 32) < 2 ^ (32 * n) := by
  rw [eval_mkP]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : c n * (2 ^ 32) ^ n ≤ (2 ^ 32 - 1) * 2 ^ (32 * n) := by
      rw [← pow_mul]
      exact Nat.mul_le_mul_right _ (by have := hc n; omega)
    have h2 : 2 ^ (32 * (n + 1)) = 2 ^ 32 * 2 ^ (32 * n) := by
      rw [Nat.mul_succ, pow_add, mul_comm]
    rw [h2]
    have h3 : (2 ^ 32 - 1) * 2 ^ (32 * n) + 2 ^ (32 * n) = 2 ^ 32 * 2 ^ (32 * n) := by
      rw [← Nat.succ_mul]
      norm_num
    omega

def Rep (x B n : ℕ) (P : (ZMod 3)[X]) : Prop :=
  ∃ p : ℕ[X], x = p.eval (2 ^ 32) ∧ Bd p B n ∧ p.map (Nat.castRingHom (ZMod 3)) = P

theorem Rep.mono {x B n B' n' : ℕ} {P : (ZMod 3)[X]} (h : Rep x B n P) (hB : B ≤ B')
    (hn : n ≤ n') : Rep x B' n' P := by
  obtain ⟨p, hx, hb, hP⟩ := h
  exact ⟨p, hx, ⟨fun i => (hb.1 i).trans hB, fun i hi => hb.2 i (by omega)⟩, hP⟩

theorem Rep.add {x y B1 B2 n m : ℕ} {P Q : (ZMod 3)[X]} (hx : Rep x B1 n P) (hy : Rep y B2 m Q) :
    Rep (x + y) (B1 + B2) (max n m) (P + Q) := by
  obtain ⟨p, rfl, hp, rfl⟩ := hx
  obtain ⟨q, rfl, hq, rfl⟩ := hy
  refine ⟨p + q, by rw [eval_add], ⟨fun i => ?_, fun i hi => ?_⟩, by rw [Polynomial.map_add]⟩
  · rw [coeff_add]
    exact Nat.add_le_add (hp.1 i) (hq.1 i)
  · rw [coeff_add, hp.2 i (by omega), hq.2 i (by omega)]

theorem coeff_mkP_mul (c : ℕ → ℕ) (n : ℕ) (q : ℕ[X]) (i : ℕ) :
    (mkP c n * q).coeff i =
      ∑ a ∈ Finset.range n, if a ≤ i then c a * q.coeff (i - a) else 0 := by
  simp only [mkP, Finset.sum_mul, finsetSum_coeff]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp

theorem Rep.mul {x y B1 B2 n m : ℕ} {P Q : (ZMod 3)[X]} (hx : Rep x B1 n P) (hy : Rep y B2 m Q) :
    Rep (x * y) (n * (B1 * B2)) (n + m - 1) (P * Q) := by
  obtain ⟨p, rfl, hp, rfl⟩ := hx
  obtain ⟨q, rfl, hq, rfl⟩ := hy
  refine ⟨p * q, by rw [eval_mul], ⟨fun i => ?_, fun i hi => ?_⟩, by rw [Polynomial.map_mul]⟩
  · rw [eq_mkP hp, coeff_mkP_mul]
    calc _ ≤ ∑ _a ∈ Finset.range n, B1 * B2 := Finset.sum_le_sum fun a _ => by
            split_ifs
            · exact Nat.mul_le_mul (hp.1 a) (hq.1 _)
            · exact Nat.zero_le _
      _ = n * (B1 * B2) := by simp
  · rw [eq_mkP hp, coeff_mkP_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [Finset.mem_range] at ha
    split_ifs
    · rw [hq.2 _ (by omega), Nat.mul_zero]
    · rfl

theorem Rep.natCast (c : ℕ) : Rep c c 1 (c : (ZMod 3)[X]) := by
  refine ⟨C c, by rw [eval_C], ⟨fun i => ?_, fun i hi => ?_⟩, by simp⟩
  · rw [coeff_C]
    split_ifs <;> omega
  · rw [coeff_C, ite_eq_right (by omega)]

theorem Rep.lin (c0 c1 : ℕ) :
    Rep (c1 * 2 ^ 32 + c0) (max c0 c1) 2 ((c1 : (ZMod 3)[X]) * X + (c0 : (ZMod 3)[X])) := by
  refine ⟨C c1 * X + C c0, by simp, ⟨fun i => ?_, fun i hi => ?_⟩, by simp⟩
  · rw [coeff_add, coeff_C_mul_X, coeff_C]
    rcases i with _ | _ | i <;> simp
  · rw [coeff_add, coeff_C_mul_X, coeff_C]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl

theorem Rep.xpow (k : ℕ) : Rep (2 ^ (32 * k)) 1 (k + 1) (X ^ k) := by
  refine ⟨X ^ k, by rw [eval_X_pow, pow_mul], ⟨fun i => ?_, fun i hi => ?_⟩, by simp⟩
  · rw [coeff_X_pow]
    split_ifs <;> omega
  · rw [coeff_X_pow, ite_eq_right (by omega)]

theorem Rep.decL_eq {x B n : ℕ} {P : (ZMod 3)[X]} (h : Rep x B n P) (hB : B < 2 ^ 32) :
    decL x = P := by
  obtain ⟨p, rfl, hp, rfl⟩ := h
  have hl := lane_eval (p := p) fun i => lt_of_le_of_lt (hp.1 i) hB
  ext j
  rw [decL, finsetSum_coeff, coeff_map, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
    exact congrArg (Nat.cast : ℕ → ZMod 3) (hl j)
  · intro i _ hij
    rw [coeff_C_mul_X_pow, ite_eq_right (Ne.symm hij)]
  · intro hj
    rw [Finset.mem_range, not_lt] at hj
    rw [coeff_C_mul_X_pow, ite_eq_left rfl]
    have h0 : lane (p.eval (2 ^ 32)) j = 0 :=
      lane_of_le (k := j) (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right
        (by norm_num) (by omega))) le_rfl
    exact (congrArg (Nat.cast : ℕ → ZMod 3) h0).trans Nat.cast_zero

theorem decL_zero : decL 0 = 0 := by simp [decL]

theorem Rep.eq_zero {B n : ℕ} {P : (ZMod 3)[X]} (h : Rep 0 B n P) (hB : B < 2 ^ 32) : P = 0 := by
  rw [← h.decL_eq hB, decL_zero]

theorem Rep.val_zero {x B : ℕ} {P : (ZMod 3)[X]} (h : Rep x B 0 P) : x = 0 := by
  obtain ⟨p, rfl, hp, -⟩ := h
  rw [eq_mkP hp, eval_mkP]
  simp

theorem Rep.coeff_eq_zero {x B n : ℕ} {P : (ZMod 3)[X]} (h : Rep x B n P) {i : ℕ} (hi : n ≤ i) :
    P.coeff i = 0 := by
  obtain ⟨p, rfl, hp, rfl⟩ := h
  rw [coeff_map, hp.2 i hi, map_zero]

theorem Rep.split {x B n : ℕ} {P : (ZMod 3)[X]} (h : Rep x B n P) (hB : B < 2 ^ 32) (k : ℕ) :
    ∃ L H, Rep (x % 2 ^ (32 * k)) B k L ∧ Rep (x / 2 ^ (32 * k)) B (n - k) H ∧
      P = L + X ^ k * H := by
  obtain ⟨p, rfl, hp, rfl⟩ := h
  have hc : ∀ i, p.coeff i < 2 ^ 32 := fun i => lt_of_le_of_lt (hp.1 i) hB
  have e : p = mkP p.coeff k + X ^ k * mkP (fun i => p.coeff (k + i)) (n - k) := by
    ext i
    rw [coeff_add, coeff_X_pow_mul', coeff_mkP, coeff_mkP]
    by_cases h1 : i < k
    · rw [ite_eq_left h1, ite_eq_right (by omega), Nat.add_zero]
    · rw [ite_eq_right h1, ite_eq_left (by omega), Nat.zero_add]
      split_ifs with h2
      · congr 1
        omega
      · exact hp.2 i (by omega)
  have hev : p.eval (2 ^ 32) = (mkP p.coeff k).eval (2 ^ 32) +
      2 ^ (32 * k) * (mkP (fun i => p.coeff (k + i)) (n - k)).eval (2 ^ 32) := by
    conv_lhs => rw [e]
    rw [eval_add, eval_mul, eval_X_pow, ← pow_mul]
  have hlt := eval_lt hc k
  refine ⟨(mkP p.coeff k).map (Nat.castRingHom (ZMod 3)),
    (mkP (fun i => p.coeff (k + i)) (n - k)).map (Nat.castRingHom (ZMod 3)),
    ⟨mkP p.coeff k, ?_, ?_, rfl⟩, ⟨mkP (fun i => p.coeff (k + i)) (n - k), ?_, ?_, rfl⟩, ?_⟩
  · rw [hev, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rw [coeff_mkP]
      split_ifs
      · exact hp.1 i
      · exact Nat.zero_le _
    · rw [coeff_mkP, ite_eq_right (by omega)]
  · rw [hev, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add]
  · refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rw [coeff_mkP]
      split_ifs
      · exact hp.1 _
      · exact Nat.zero_le _
    · rw [coeff_mkP, ite_eq_right (by omega)]
  · conv_lhs => rw [e]
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X]

theorem Rep.of_lanes {x k B : ℕ} (hx : x < 2 ^ (32 * k)) (hB : B < 2 ^ 32)
    (hl : ∀ i < k, lane x i ≤ B) : Rep x B k (decL x) := by
  have hp : ∀ i, (mkP (lane x) k).coeff i < 2 ^ 32 := fun i => by
    rw [coeff_mkP]
    split_ifs
    · exact lane_lt _ _
    · norm_num
  have e : x = (mkP (lane x) k).eval (2 ^ 32) := by
    apply lane_ext
    intro i
    rw [lane_eval hp, coeff_mkP]
    split_ifs with h
    · rfl
    · exact lane_of_le hx (by omega)
  have h : Rep x B k ((mkP (lane x) k).map (Nat.castRingHom (ZMod 3))) := by
    refine ⟨_, e, ⟨fun i => ?_, fun i hi => ?_⟩, rfl⟩
    · rw [coeff_mkP]
      split_ifs with h
      · exact hl i h
      · exact Nat.zero_le _
    · rw [coeff_mkP, ite_eq_right (by omega)]
  rwa [h.decL_eq hB]

theorem repK_eq (L v : ℕ) : repK L v = (mkP (fun _ => v) L).eval (2 ^ 32) := by
  change v * ((1 <<< (32 * L) - 1) / 4294967295) = _
  rw [eval_mkP, ← Finset.mul_sum, Nat.geomSum_eq (by norm_num), ← pow_mul, Nat.shiftLeft_eq,
    one_mul]
  norm_num

theorem lane_repK {L v : ℕ} (hv : v < 2 ^ 32) (i : ℕ) :
    lane (repK L v) i = if i < L then v else 0 := by
  rw [repK_eq, lane_eval, coeff_mkP]
  intro j
  rw [coeff_mkP]
  split_ifs
  · exact hv
  · norm_num

theorem red3_eq (M15 x : ℕ) : red3 M15 x = x - 3 * (((x * 43691) >>> 17) &&& M15) := rfl

theorem lane_shift17 (y i : ℕ) : lane (y >>> 17) i % 2 ^ 15 = lane y i / 2 ^ 17 := by
  rw [lane, lane, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, mul_comm,
    ← Nat.div_div_eq_div_mul]
  generalize y / 2 ^ (32 * i) = w
  norm_num
  omega

theorem Rep.red3 {x B n L M15 : ℕ} {P : (ZMod 3)[X]} (h : Rep x B n P) (hB : B < 2 ^ 16)
    (hn : n ≤ L) (hM : M15 = repK L 32767) : Rep (red3 M15 x) 2 n P := by
  obtain ⟨p, rfl, hp, rfl⟩ := h
  have hcB : ∀ i, p.coeff i < 2 ^ 16 := fun i => lt_of_le_of_lt (hp.1 i) hB
  set Q := mkP (fun i => p.coeff i / 3) n
  set R := mkP (fun i => p.coeff i % 3) n
  have hx : p.eval (2 ^ 32) = R.eval (2 ^ 32) + 3 * Q.eval (2 ^ 32) := by
    rw [eq_mkP hp, eval_mkP, eval_mkP, eval_mkP, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, ← add_mul, Nat.mod_add_div]
  have hy : ∀ i, lane (p.eval (2 ^ 32) * 43691) i = p.coeff i * 43691 := by
    intro i
    have e : p.eval (2 ^ 32) * 43691 = (p * C 43691).eval (2 ^ 32) := by rw [eval_mul, eval_C]
    rw [e, lane_eval, coeff_mul_C]
    intro j
    rw [coeff_mul_C]
    have := hcB j
    omega
  have hz : ((p.eval (2 ^ 32) * 43691) >>> 17) &&& M15 = Q.eval (2 ^ 32) := by
    apply lane_ext
    intro i
    have hq : ∀ j, Q.coeff j < 2 ^ 32 := fun j => by
      rw [coeff_mkP]
      split_ifs
      · have := hcB j
        omega
      · norm_num
    rw [lane_and, hM, lane_repK (by norm_num), lane_eval hq, coeff_mkP]
    have h15 : (32767 : ℕ) = 2 ^ 15 - 1 := by norm_num
    by_cases hi : i < L
    · rw [ite_eq_left hi, h15, Nat.and_two_pow_sub_one_eq_mod, lane_shift17, hy]
      have := hcB i
      split_ifs with h1
      · omega
      · rw [hp.2 i (by omega)]
        rfl
    · rw [ite_eq_right hi, Nat.and_zero, ite_eq_right (by omega)]
  refine ⟨R, ?_, ⟨fun i => ?_, fun i hi => ?_⟩, ?_⟩
  · rw [red3_eq, hz]
    omega
  · rw [coeff_mkP]
    split_ifs
    · have := Nat.mod_lt (p.coeff i) (by norm_num : 3 > 0)
      omega
    · exact Nat.zero_le _
  · rw [coeff_mkP, ite_eq_right (by omega)]
  · ext i
    rw [coeff_map, coeff_map, coeff_mkP]
    split_ifs with h1
    · simp only [eq_natCast, ZMod.natCast_mod]
    · rw [hp.2 i (by omega)]

open CFSG.KC.Loop

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem normK_succ (sk G M15 ML n N : ℕ) : normK sk G M15 ML (n + 1) N =
    if N >>> sk = 0 then N else normK sk G M15 ML n (red3 M15 ((N &&& ML) + (N >>> sk) * G)) := by
  change strictN (N >>> sk) (fun H => Bool.rec (motive := fun _ => Nat)
    (strictN (red3 M15 (Nat.add (Nat.land N ML) (Nat.mul H G))) (normK sk G M15 ML n)) N
      (Nat.beq H 0)) = _
  simp only [strictN_eq]
  by_cases h : N >>> sk = 0
  · rw [ite_eq_left h, h]
    rfl
  · rw [ite_eq_right h]
    cases hb : Nat.beq (N >>> sk) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h

@[expose] noncomputable def powR (sk G M15 ML fuel a e j : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun j ih acc => strictN (mulK sk G M15 ML fuel acc acc) (fun sq =>
      strictN (nIf(Nat.blt (nat_lit 0) (Nat.land e (Nat.shiftLeft (nat_lit 1) j)),
        mulK sk G M15 ML fuel sq a, sq)) ih)) j

theorem powK_eq (sk G M15 ML fuel a e nb : ℕ) :
    powK sk G M15 ML fuel a e nb = powR sk G M15 ML fuel a e nb 1 := rfl

theorem powR_succ (sk G M15 ML fuel a e j acc : ℕ) :
    powR sk G M15 ML fuel a e (j + 1) acc = powR sk G M15 ML fuel a e j
      (if e / 2 ^ j % 2 = 1 then mulK sk G M15 ML fuel (mulK sk G M15 ML fuel acc acc) a
        else mulK sk G M15 ML fuel acc acc) := by
  change strictN (mulK sk G M15 ML fuel acc acc) (fun sq =>
      strictN (Bool.rec (motive := fun _ => Nat) sq (mulK sk G M15 ML fuel sq a)
        (Nat.blt 0 (e &&& (1 <<< j)))) (powR sk G M15 ML fuel a e j)) = _
  simp only [strictN_eq]
  by_cases h : e / 2 ^ j % 2 = 1
  · rw [ite_eq_left h]
    have hb : Nat.blt 0 (e &&& (1 <<< j)) = true := by
      rw [Nat.blt_eq, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow,
        Nat.testBit_eq_decide_div_mod_eq, decide_eq_true h]
      simp
    rw [hb]
  · rw [ite_eq_right h]
    have hb : Nat.blt 0 (e &&& (1 <<< j)) = false := by
      rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq,
        decide_eq_false h]
      simp only [Bool.toNat_false, zero_mul]
      rfl
    rw [hb]

theorem bitsLe_lt {e nb : ℕ} (h : bitsLe e nb = true) : e < 2 ^ nb := by
  have h1 : e >>> nb = 0 := Nat.eq_of_beq_eq_true h
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact h1

noncomputable def qf (f : (ZMod 3)[X]) : (ZMod 3)[X] →+* (ZMod 3)[X] ⧸ Ideal.span {f} :=
  Ideal.Quotient.mk _

theorem dvd_of_qf {f a b : (ZMod 3)[X]} (h : qf f a = qf f b) : f ∣ a - b :=
  Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)

theorem three_poly : (3 : (ZMod 3)[X]) = 0 := by
  have h : ((3 : ℕ) : (ZMod 3)[X]) = 0 := CharP.cast_eq_zero _ 3
  simpa using h

theorem qf_three (f : (ZMod 3)[X]) : (3 : (ZMod 3)[X] ⧸ Ideal.span {f}) = 0 := by
  rw [← map_ofNat (qf f) 3, three_poly, map_zero]

structure Env (k G M15 ML : ℕ) (f : (ZMod 3)[X]) : Prop where
  one_lt : 1 < k
  lt : k < 16384
  hML : ML = 2 ^ (32 * k) - 1
  hM15 : M15 = repK (2 * k + 2) 32767
  hG : ∃ Gp, Rep G 2 k Gp ∧ qf f (X ^ k) = qf f Gp

variable {k G M15 ML : ℕ} {f : (ZMod 3)[X]}

theorem Env.red3' (E : Env k G M15 ML f) {x B n : ℕ} {P : (ZMod 3)[X]} (h : Rep x B n P)
    (hB : B < 2 ^ 16) (hn : n ≤ k) : Rep (red3 M15 x) 2 k P :=
  (h.red3 hB (by omega) E.hM15).mono le_rfl hn

theorem Env.normK (E : Env k G M15 ML f) (fuel : ℕ) : ∀ (d x : ℕ) (P : (ZMod 3)[X]), Rep x 2 d P →
    k ≤ d → d + 1 ≤ 2 * k → d ≤ fuel + k →
    ∃ Q, Rep (normK (32 * k) G M15 ML fuel x) 2 k Q ∧ qf f Q = qf f P := by
  induction fuel with
  | zero =>
    intro d x P h h1 h2 h3
    exact ⟨P, h.mono le_rfl (by omega), rfl⟩
  | succ n ih =>
    intro d x P h h1 h2 h3
    obtain ⟨Gp, hG, hXG⟩ := E.hG
    obtain ⟨L, H, hL, hH, hP⟩ := h.split (by norm_num) k
    rw [normK_succ, Nat.shiftRight_eq_div_pow]
    by_cases h0 : x / 2 ^ (32 * k) = 0
    · rw [ite_eq_left h0]
      rw [h0] at hH
      have hx : x % 2 ^ (32 * k) = x := Nat.mod_eq_of_lt (by
        rcases Nat.lt_or_ge x (2 ^ (32 * k)) with h4 | h4
        · exact h4
        · exact absurd h0 (Nat.div_pos h4 (by positivity)).ne')
      rw [hx] at hL
      refine ⟨L, hL, ?_⟩
      rw [hP, hH.eq_zero (by norm_num), mul_zero, add_zero]
    · have hand : x &&& ML = x % 2 ^ (32 * k) := by rw [E.hML, Nat.and_two_pow_sub_one_eq_mod]
      rw [ite_eq_right h0, hand]
      have hd : k + 1 ≤ d := by
        by_contra hd
        rw [Nat.sub_eq_zero_of_le (by omega)] at hH
        exact h0 hH.val_zero
      have hs := hL.add (hH.mul hG)
      have hr := (hs.red3 (by have := E.lt; omega) (by omega) E.hM15).mono le_rfl
        (by omega : max k (d - k + k - 1) ≤ d - 1)
      obtain ⟨Q, hQ, hQe⟩ := ih (d - 1) _ _ hr (by omega) (by omega) (by omega)
      refine ⟨Q, hQ, ?_⟩
      rw [hQe, hP, map_add, map_add, map_mul, map_mul, ← hXG, mul_comm]

theorem Env.mulK (E : Env k G M15 ML f) {a b : ℕ} {A Bq : (ZMod 3)[X]} (ha : Rep a 2 k A)
    (hb : Rep b 2 k Bq) :
    ∃ Q, Rep (mulK (32 * k) G M15 ML (k + k) a b) 2 k Q ∧ qf f Q = qf f A * qf f Bq := by
  have hr := (ha.mul hb).red3 (by have := E.lt; omega) (by omega : k + k - 1 ≤ 2 * k + 2) E.hM15
  have := E.one_lt
  obtain ⟨Q, hQ, hQe⟩ := E.normK (k + k) (k + k - 1) _ _ hr (by omega) (by omega) (by omega)
  exact ⟨Q, hQ, by rw [hQe, map_mul]⟩

theorem Env.powR (E : Env k G M15 ML f) {a : ℕ} {A : (ZMod 3)[X]} (ha : Rep a 2 k A) (e j : ℕ) :
    ∀ acc (Acc : (ZMod 3)[X]), Rep acc 2 k Acc → ∃ Q,
      Rep (powR (32 * k) G M15 ML (k + k) a e j acc) 2 k Q ∧
        qf f Q = qf f Acc ^ 2 ^ j * qf f A ^ (e % 2 ^ j) := by
  induction j with
  | zero =>
    intro acc Acc h
    exact ⟨Acc, h, by simp [Nat.mod_one]⟩
  | succ j ih =>
    intro acc Acc h
    rw [powR_succ]
    obtain ⟨S, hS, hSe⟩ := E.mulK h h
    rw [Nat.mod_pow_succ]
    split_ifs with hb
    · obtain ⟨S2, hS2, hS2e⟩ := E.mulK hS ha
      obtain ⟨Q, hQ, hQe⟩ := ih _ _ hS2
      refine ⟨Q, hQ, ?_⟩
      rw [hQe, hS2e, hSe, hb]
      ring
    · obtain ⟨Q, hQ, hQe⟩ := ih _ _ hS
      refine ⟨Q, hQ, ?_⟩
      have hb0 : e / 2 ^ j % 2 = 0 := by omega
      rw [hQe, hSe, hb0]
      ring

theorem Rep.one (hk : 1 ≤ k) : Rep 1 2 k 1 := by
  have h := (Rep.natCast 1).mono (by norm_num : 1 ≤ 2) hk
  rwa [Nat.cast_one] at h

theorem Env.powK (E : Env k G M15 ML f) {a e nb : ℕ} {A : (ZMod 3)[X]} (ha : Rep a 2 k A)
    (he : e < 2 ^ nb) :
    ∃ Q, Rep (powK (32 * k) G M15 ML (k + k) a e nb) 2 k Q ∧ qf f Q = qf f A ^ e := by
  obtain ⟨Q, hQ, hQe⟩ := E.powR ha e nb 1 1 (Rep.one (by have := E.one_lt; omega))
  refine ⟨Q, hQ, ?_⟩
  rw [hQe, map_one, one_pow, one_mul, Nat.mod_eq_of_lt he]

theorem le3_of_and {v : ℕ} (hv : v < 2 ^ 32) (h : v &&& 4294967292 = 0) : v ≤ 3 := by
  have : v < 2 ^ 2 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases hi32 : i < 32
    · have h1 := congrArg (Nat.testBit · i) h
      simp only [Nat.testBit_and, Nat.zero_testBit] at h1
      have h2 : (4294967292 : ℕ).testBit i = true := by
        interval_cases i <;> decide
      rw [h2, Bool.and_true] at h1
      exact h1
    · exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
  omega

theorem rep_land {x : ℕ} (hML : ML = 2 ^ (32 * k) - 1) (hm : x &&& repK k 4294967292 = 0) :
    Rep (x &&& ML) 3 k (decL (x &&& ML)) := by
  rw [hML, Nat.and_two_pow_sub_one_eq_mod]
  refine Rep.of_lanes (Nat.mod_lt _ (by positivity)) (by norm_num) fun i hi => ?_
  rw [lane_mod hi]
  have h1 := congrArg (lane · i) hm
  simp only [lane_and, lane_repK (by norm_num : (4294967292 : ℕ) < 2 ^ 32), ite_eq_left hi] at h1
  have h0 : lane 0 i = 0 := by simp [lane]
  rw [h0] at h1
  exact le3_of_and (lane_lt x i) h1

theorem Env.rep_of_checks (E : Env k G M15 ML f) {w : ℕ}
    (h1 : Nat.beq (Nat.land w (repK k 4294967292)) 0 = true)
    (h2 : Nat.beq (red3 M15 (Nat.land w ML)) w = true) : ∃ W, Rep w 2 k W := by
  have h := E.red3' (rep_land E.hML (Nat.eq_of_beq_eq_true h1)) (by norm_num) le_rfl
  exact ⟨_, Eq.mp (congrArg (fun x => Rep x 2 k _) (Nat.eq_of_beq_eq_true h2)) h⟩

theorem setup_env {F : ℕ} (hs : setupK k F G M15 ML = true) :
    Env k G M15 ML (decL F) ∧ (decL F).coeff k ≠ 0 := by
  unfold setupK at hs
  simp only [bAnd_eq] at hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  have hk1 : 1 < k := by rwa [Nat.blt_eq] at h1
  have hk2 : k < 16384 := by rwa [Nat.blt_eq] at h2
  have hML : ML = 2 ^ (32 * k) - 1 := by
    rw [Nat.eq_of_beq_eq_true h3]
    change (1 <<< (32 * k)) - 1 = _
    rw [Nat.shiftLeft_eq, one_mul]
  have hM15 : M15 = repK (2 * k + 2) 32767 := by
    rw [Nat.eq_of_beq_eq_true h4]
    congr 1
    change k + k + 2 = _
    omega
  have hF1 : F / 2 ^ (32 * k) = 1 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.eq_of_beq_eq_true h5
  have hL3 := rep_land hML (Nat.eq_of_beq_eq_true h6)
  set Lf := decL (F &&& ML)
  have hL2 : Rep (F &&& ML) 2 k Lf := by
    have h := hL3.red3 (by norm_num) (by omega : k ≤ 2 * k + 2) hM15
    exact Eq.mp (congrArg (fun x => Rep x 2 k Lf) (Nat.eq_of_beq_eq_true h7)) h
  have hGr : Rep G 2 k (Lf + Lf) := by
    rw [Nat.eq_of_beq_eq_true h8]
    exact ((hL2.add hL2).red3 (by norm_num) (by omega) hM15).mono le_rfl (by omega)
  have hFe : F = (F &&& ML) + 2 ^ (32 * k) := by
    rw [hML, Nat.and_two_pow_sub_one_eq_mod]
    have := Nat.mod_add_div F (2 ^ (32 * k))
    rw [hF1, mul_one] at this
    omega
  have hF : decL F = Lf + X ^ k := by
    rw [hFe]
    exact (hL2.add (Rep.xpow k)).decL_eq (by norm_num)
  refine ⟨⟨hk1, hk2, hML, hM15, Lf + Lf, hGr, ?_⟩, ?_⟩
  · apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    rw [hF]
    exact ⟨1, by linear_combination (-Lf) * three_poly⟩
  · rw [hF, coeff_add, coeff_X_pow_self, hL2.coeff_eq_zero le_rfl, zero_add]
    exact one_ne_zero

theorem rep_X (hk : 2 ≤ k) : Rep 4294967296 2 k X := by
  have h := (Rep.lin 0 1).mono (by norm_num : max 0 1 ≤ 2) hk
  simpa using h

theorem rep_X1 (hk : 2 ≤ k) : Rep 4294967297 2 k (X + 1) := by
  have h := (Rep.lin 1 1).mono (by norm_num : max 1 1 ≤ 2) hk
  simpa using h

theorem rep_X2 (hk : 2 ≤ k) : Rep 4294967298 2 k (X + 2) := by
  have h := (Rep.lin 2 1).mono (by norm_num : max 2 1 ≤ 2) hk
  simpa using h

end CFSG.KC.Misc.Ree

end
