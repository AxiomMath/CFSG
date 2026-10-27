module

public import Mathlib.Algebra.Group.Basic
public import Certificates.Data.Kernel.Pc3.Coll
import CFSG.Certificates.Kernel.Spor.PK.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.Defs.PartialOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.Pc3

open CFSG.KC.Pc3

variable {G : Type*} [Group G]

@[expose] noncomputable def nv (x : ℕ → G) (n u : ℕ) : G :=
  ((List.range n).map fun k => x k ^ dg u k).prod

structure PcRel (x : ℕ → G) (n PW CJ : ℕ) : Prop where
  cube : ∀ k < n, x k ^ 3 = nv x n (f32 PW k)
  conj : ∀ i j, i < j → j < n → (x i)⁻¹ * x j * x i = nv x n (f32 CJ (16 * i + j))

theorem pc3S_strictN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem pc3S_strictB (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem pc3S_band {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem pc3S_bif {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem pc3S_rep_zero (g : ℕ → ℕ) (s : ℕ) : rep 0 g s = s := rfl

theorem pc3S_rep_one (g : ℕ → ℕ) (s : ℕ) : rep 1 g s = g s :=
  pc3S_strictN (g s) (fun s₁ => Bool.rec (motive := fun _ => ℕ) (g s₁) s₁ (Nat.beq 1 1))

theorem pc3S_rep_two (g : ℕ → ℕ) (s : ℕ) : rep 2 g s = g (g s) :=
  pc3S_strictN (g s) (fun s₁ => Bool.rec (motive := fun _ => ℕ) (g s₁) s₁ (Nat.beq 2 1))

theorem pc3S_four_pow (k : ℕ) : 2 ^ (k <<< 1) = 4 ^ k := by
  rw [Nat.shiftLeft_eq, pow_one, Nat.mul_comm, pow_mul]
  norm_num

theorem pc3S_dg (u k : ℕ) : dg u k = u / 4 ^ k % 4 := by
  change (u >>> (k <<< 1)) &&& 3 = _
  rw [Nat.shiftRight_eq_div_pow, pc3S_four_pow]
  exact Nat.and_two_pow_sub_one_eq_mod (u / 4 ^ k) 2

theorem pc3S_low (u k : ℕ) : lowV u k = u % 4 ^ k := by
  change u &&& ((1 <<< (k <<< 1)) - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, pc3S_four_pow]

theorem pc3S_high (u k : ℕ) : highV u k = 4 ^ (k + 1) * (u / 4 ^ (k + 1)) := by
  change (u >>> ((k + 1) <<< 1)) <<< ((k + 1) <<< 1) = _
  rw [Nat.shiftLeft_eq (u >>> ((k + 1) <<< 1)), Nat.shiftRight_eq_div_pow, pc3S_four_pow,
    Nat.mul_comm (u / 4 ^ (k + 1))]

theorem pc3S_dg_lt {a i : ℕ} (h : a < 4 ^ i) : dg a i = 0 := by
  rw [pc3S_dg, Nat.div_eq_of_lt h, Nat.zero_mod]

theorem pc3S_dg_zero (i : ℕ) : dg 0 i = 0 := by
  rw [pc3S_dg, Nat.zero_div, Nat.zero_mod]

theorem pc3S_dg_ge {n u i : ℕ} (h : u < 4 ^ n) (hi : n ≤ i) : dg u i = 0 :=
  pc3S_dg_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hi))

theorem pc3S_lt_of_dg {n u j : ℕ} (hu : u < 4 ^ n) (h : dg u j ≠ 0) : j < n := by
  by_contra hj
  exact h (pc3S_dg_ge hu (by omega))

theorem pc3S_dgS (a q m i : ℕ) (ha : a < 4 ^ m) :
    dg (a + 4 ^ m * q) i = if i < m then dg a i else dg q (i - m) := by
  have hpos : 0 < 4 ^ i := by positivity
  simp only [pc3S_dg]
  split_ifs with hi
  · obtain ⟨d, rfl⟩ : ∃ d, m = i + 1 + d := ⟨m - i - 1, by omega⟩
    have e : a + 4 ^ (i + 1 + d) * q = a + 4 ^ i * (4 * (4 ^ d * q)) := by ring
    rw [e, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]
  · obtain ⟨d, rfl⟩ : ∃ d, i = m + d := ⟨i - m, by omega⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem pc3S_dg_mul (q m i : ℕ) : dg (4 ^ m * q) i = if i < m then 0 else dg q (i - m) := by
  have h := pc3S_dgS 0 q m i (by positivity)
  rwa [Nat.zero_add, pc3S_dg_zero] at h

theorem pc3S_dg_of_mod {c m i : ℕ} (h : c % 4 ^ m = 0) (hi : i < m) : dg c i = 0 := by
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero h
  rw [pc3S_dg_mul, if_pos hi]

theorem pc3S_dg_small {d : ℕ} (hd : d < 4) (j : ℕ) : dg d j = if j = 0 then d else 0 := by
  rw [pc3S_dg]
  split_ifs with hj
  · rw [hj, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hd]
  · have h4 : (4 : ℕ) ≤ 4 ^ j := by
      calc (4 : ℕ) = 4 ^ 1 := (pow_one 4).symm
        _ ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hj)
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hd h4), Nat.zero_mod]

theorem pc3S_dg3 (u i : ℕ) :
    dg u i = 3 ↔ u.testBit (2 * i) = true ∧ u.testBit (2 * i + 1) = true := by
  rw [pc3S_dg, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    decide_eq_true_iff, decide_eq_true_iff, pow_succ, ← Nat.div_div_eq_div_mul, pow_mul,
    show (2 : ℕ) ^ 2 = 4 by norm_num]
  generalize u / 4 ^ i = q
  omega

def pc3NW (n u : ℕ) : Prop := u < 4 ^ n ∧ ∀ i, dg u i < 3

theorem pc3S_vecOK {n u : ℕ} (hn : n ≤ 16) : vecOK n u = true ↔ pc3NW n u := by
  have e : vecOK n u = (Nat.blt u (4 ^ n) && Nat.beq ((u &&& (u >>> 1)) &&& 1431655765) 0) := by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.beq ((u &&& (u >>> 1)) &&& 1431655765) 0) (Nat.blt u (1 <<< (n <<< 1))) = _
    rw [Nat.one_shiftLeft, pc3S_four_pow]
    cases Nat.blt u (4 ^ n) <;> rfl
  rw [e, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i => ?_⟩
    have h4 : dg u i < 4 := by
      rw [pc3S_dg]
      exact Nat.mod_lt _ (by norm_num)
    by_contra h3
    have h5 : dg u i = 3 := by omega
    have hi : i < 16 := by
      by_contra hi
      rw [pc3S_dg_ge (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hn)) (by omega)] at h5
      exact absurd h5 (by norm_num)
    obtain ⟨b1, b2⟩ := (pc3S_dg3 u i).1 h5
    have hM : ∀ i < 16, Nat.testBit 1431655765 (2 * i) = true := by decide
    have h6 : Nat.testBit ((u &&& (u >>> 1)) &&& 1431655765) (2 * i) = false := by
      rw [h2, Nat.zero_testBit]
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, hM i hi, b1,
      show 1 + 2 * i = 2 * i + 1 by omega, b2] at h6
    exact absurd h6 (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Nat.eq_of_testBit_eq fun b => ?_⟩
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit]
    by_cases hb : b < 32
    · have hM : ∀ b < 32, Nat.testBit 1431655765 b = decide (b % 2 = 0) := by decide
      rw [hM b hb]
      by_cases hp : b % 2 = 0
      · obtain ⟨i, rfl⟩ : ∃ i, b = 2 * i := ⟨b / 2, by omega⟩
        have hn3 : ¬ (u.testBit (2 * i) = true ∧ u.testBit (2 * i + 1) = true) := fun h => by
          have h7 := (pc3S_dg3 u i).2 h
          have h8 := h2 i
          omega
        rw [show 1 + 2 * i = 2 * i + 1 by omega]
        cases h1' : u.testBit (2 * i) <;> cases h2' : u.testBit (2 * i + 1) <;> simp_all
      · simp [hp]
    · have hlt : (1431655765 : ℕ) < 2 ^ b :=
        lt_of_lt_of_le (by norm_num : (1431655765 : ℕ) < 2 ^ 32)
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hlt]
      simp

theorem pc3S_NW_zero {n : ℕ} : pc3NW n 0 :=
  ⟨by positivity, fun i => by rw [pc3S_dg_zero]; norm_num⟩

theorem pc3S_NW_sum {n a q m : ℕ} (ha : pc3NW n a) (hq : pc3NW n (4 ^ m * q)) (ham : a < 4 ^ m) :
    pc3NW n (a + 4 ^ m * q) := by
  refine ⟨?_, fun i => ?_⟩
  · rcases Nat.eq_zero_or_pos q with rfl | hq0
    · simpa using ha.1
    · have h1 : 4 ^ m ≤ 4 ^ m * q := Nat.le_mul_of_pos_right _ hq0
      have hmn : m ≤ n := by
        by_contra hmn
        have h3 : 4 ^ n ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h4 := hq.1
        omega
      have hpow : 4 ^ m * 4 ^ (n - m) = 4 ^ n := by rw [← pow_add, Nat.add_sub_of_le hmn]
      have h2 : q < 4 ^ (n - m) := by
        apply Nat.lt_of_mul_lt_mul_left (a := 4 ^ m)
        rw [hpow]
        exact hq.1
      calc a + 4 ^ m * q < 4 ^ m * (q + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ 4 ^ m * 4 ^ (n - m) := Nat.mul_le_mul_left _ h2
        _ = 4 ^ n := hpow
  · rw [pc3S_dgS a q m i ham]
    split_ifs with hi
    · exact ha.2 i
    · have h := hq.2 i
      rwa [pc3S_dg_mul, if_neg hi] at h

theorem pc3S_NW_split {n u : ℕ} (hu : pc3NW n u) (m : ℕ) :
    pc3NW n (u % 4 ^ m) ∧ pc3NW n (4 ^ m * (u / 4 ^ m)) := by
  have hpos : 0 < 4 ^ m := by positivity
  have e : ∀ i, dg u i = if i < m then dg (u % 4 ^ m) i else dg (u / 4 ^ m) (i - m) := by
    intro i
    have h := pc3S_dgS (u % 4 ^ m) (u / 4 ^ m) m i (Nat.mod_lt _ hpos)
    rwa [Nat.mod_add_div] at h
  refine ⟨⟨lt_of_le_of_lt (Nat.mod_le _ _) hu.1, fun i => ?_⟩,
    ⟨lt_of_le_of_lt (Nat.mul_div_le _ _) hu.1, fun i => ?_⟩⟩
  · by_cases hi : i < m
    · have h := e i
      rw [if_pos hi] at h
      rw [← h]
      exact hu.2 i
    · rw [pc3S_dg_lt (lt_of_lt_of_le (Nat.mod_lt _ hpos)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      norm_num
  · rw [pc3S_dg_mul]
    split_ifs with hi
    · norm_num
    · have h := e i
      rw [if_neg hi] at h
      rw [← h]
      exact hu.2 i

theorem pc3S_NW_digit {n k d : ℕ} (hk : k < n) (hd : d < 3) : pc3NW n (4 ^ k * d) := by
  refine ⟨?_, fun i => ?_⟩
  · have hpos : 0 < 4 ^ k := by positivity
    calc 4 ^ k * d < 4 ^ k * 4 := by nlinarith
      _ = 4 ^ (k + 1) := (pow_succ 4 k).symm
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hk
  · rw [pc3S_dg_mul]
    split_ifs
    · norm_num
    · rw [pc3S_dg_small (d := d) (by omega)]
      split_ifs <;> omega

noncomputable def pc3nvF (y : ℕ → G) (m : ℕ) (e : ℕ → ℕ) : G :=
  ((List.range m).map fun k => y k ^ e k).prod

theorem pc3S_nvF_succ (y : ℕ → G) (m : ℕ) (e : ℕ → ℕ) :
    pc3nvF y (m + 1) e = pc3nvF y m e * y m ^ e m := by
  simp [pc3nvF, List.range_succ]

theorem pc3S_nvF_one (y : ℕ → G) {e : ℕ → ℕ} : ∀ m, (∀ i < m, e i = 0) → pc3nvF y m e = 1
  | 0, _ => by simp [pc3nvF]
  | m + 1, h => by
    rw [pc3S_nvF_succ, pc3S_nvF_one y m (fun i hi => h i (by omega)), h m (by omega)]
    simp

theorem pc3S_nvF_congr {y y' : ℕ → G} {e e' : ℕ → ℕ} :
    ∀ m, (∀ i < m, y i ^ e i = y' i ^ e' i) → pc3nvF y m e = pc3nvF y' m e'
  | 0, _ => by simp [pc3nvF]
  | m + 1, h => by
    rw [pc3S_nvF_succ, pc3S_nvF_succ, pc3S_nvF_congr m (fun i hi => h i (by omega)),
      h m (by omega)]

theorem pc3S_conj_pow (a b : G) (k : ℕ) : (a⁻¹ * b * a) ^ k = a⁻¹ * b ^ k * a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem pc3S_nvF_conj (y : ℕ → G) (a : G) (e : ℕ → ℕ) :
    ∀ m, pc3nvF (fun i => a⁻¹ * y i * a) m e = a⁻¹ * pc3nvF y m e * a
  | 0 => by simp [pc3nvF]
  | m + 1 => by
    have h1 : pc3nvF (fun i => a⁻¹ * y i * a) (m + 1) e =
        pc3nvF (fun i => a⁻¹ * y i * a) m e * (a⁻¹ * y m * a) ^ e m :=
      pc3S_nvF_succ _ _ _
    rw [h1, pc3S_nvF_succ, pc3S_nvF_conj y a e m, pc3S_conj_pow]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem pc3S_nvF_single (y : ℕ → G) {e : ℕ → ℕ} {k : ℕ} :
    ∀ m, k < m → (∀ i < m, i ≠ k → e i = 0) → pc3nvF y m e = y k ^ e k
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, h, he => by
    rw [pc3S_nvF_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · rw [pc3S_nvF_single y m h' (fun i hi hik => he i (by omega) hik), he m (by omega) (by omega),
        pow_zero, mul_one]
    · rw [pc3S_nvF_one y _ (fun i hi => he i (by omega) (by omega)), one_mul]

theorem pc3S_nvF_split (y : ℕ → G) {m : ℕ} {e e' : ℕ → ℕ} (he : ∀ i, m ≤ i → e i = 0)
    (he' : ∀ i < m, e' i = 0) :
    ∀ n, pc3nvF y n (fun i => e i + e' i) = pc3nvF y n e * pc3nvF y n e'
  | 0 => by simp [pc3nvF]
  | n + 1 => by
    have h1 : pc3nvF y (n + 1) (fun i => e i + e' i) =
        pc3nvF y n (fun i => e i + e' i) * y n ^ (e n + e' n) := pc3S_nvF_succ _ _ _
    rw [h1, pc3S_nvF_succ, pc3S_nvF_succ, pc3S_nvF_split y he he' n]
    by_cases h : n < m
    · rw [he' n h, pc3S_nvF_one y n (fun i hi => he' i (by omega))]
      simp
    · rw [he n (by omega)]
      simp [mul_assoc]

theorem pc3S_nv_zero (x : ℕ → G) (n : ℕ) : nv x n 0 = 1 :=
  pc3S_nvF_one x n (fun i _ => pc3S_dg_zero i)

theorem pc3S_nvSum (x : ℕ → G) {n a q m : ℕ} (ha : a < 4 ^ m) :
    nv x n (a + 4 ^ m * q) = nv x n a * nv x n (4 ^ m * q) := by
  have hge : ∀ i, m ≤ i → dg a i = 0 := fun i hi =>
    pc3S_dg_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi))
  have h1 : dg (a + 4 ^ m * q) = fun i => dg a i + dg (4 ^ m * q) i := by
    funext i
    rw [pc3S_dgS a q m i ha, pc3S_dg_mul]
    split_ifs with hi
    · rw [Nat.add_zero]
    · rw [hge i (by omega), Nat.zero_add]
  change pc3nvF x n (dg (a + 4 ^ m * q)) = pc3nvF x n (dg a) * pc3nvF x n (dg (4 ^ m * q))
  rw [h1]
  exact pc3S_nvF_split x (m := m) hge (fun i hi => by rw [pc3S_dg_mul, if_pos hi]) n

theorem pc3S_nv_digit (x : ℕ → G) {n k d : ℕ} (hk : k < n) (hd : d < 4) :
    nv x n (4 ^ k * d) = x k ^ d := by
  have h0 : dg (4 ^ k * d) k = d := by
    rw [pc3S_dg_mul, if_neg (lt_irrefl k), Nat.sub_self, pc3S_dg_small hd, if_pos rfl]
  have hz : ∀ i < n, i ≠ k → dg (4 ^ k * d) i = 0 := by
    intro i _ hik
    rw [pc3S_dg_mul]
    split_ifs with h
    · rfl
    · rw [pc3S_dg_small hd, if_neg (show i - k ≠ 0 by omega)]
  change pc3nvF x n (dg (4 ^ k * d)) = _
  rw [pc3S_nvF_single x n hk hz, h0]

theorem pc3S_decomp (x : ℕ → G) {n : ℕ} (u : ℕ) {k : ℕ} (hk : k < n) :
    nv x n u = nv x n (u % 4 ^ k) * x k ^ dg u k * nv x n (4 ^ (k + 1) * (u / 4 ^ (k + 1))) := by
  have hq : u / 4 ^ k = dg u k + 4 * (u / 4 ^ (k + 1)) := by
    rw [pc3S_dg, pow_succ, ← Nat.div_div_eq_div_mul]
    generalize u / 4 ^ k = q
    omega
  have e1 : u = u % 4 ^ k + 4 ^ k * (dg u k + 4 * (u / 4 ^ (k + 1))) := by
    rw [← hq, Nat.mod_add_div]
  have e2 : 4 ^ k * (dg u k + 4 * (u / 4 ^ (k + 1))) =
      4 ^ k * dg u k + 4 ^ (k + 1) * (u / 4 ^ (k + 1)) := by
    rw [pow_succ]
    ring
  have hd : dg u k < 4 := by
    rw [pc3S_dg]
    exact Nat.mod_lt _ (by norm_num)
  have h3 : 4 ^ k * dg u k < 4 ^ (k + 1) := by
    have hpos : 0 < 4 ^ k := by positivity
    rw [pow_succ]
    nlinarith
  conv_lhs => rw [e1]
  rw [pc3S_nvSum x (Nat.mod_lt u (by positivity : 0 < 4 ^ k)), e2, pc3S_nvSum x h3, pc3S_nv_digit x hk hd,
    mul_assoc]

def pc3MulOK (x : ℕ → G) (n : ℕ) (M : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∀ s, pc3NW n s → pc3NW n (M j s) ∧ nv x n (M j s) = nv x n s * x j ∧ M j s % 4 ^ j = s % 4 ^ j

noncomputable def pc3S_F (z y : ℕ) (Gs : ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) z
    (fun j acc => CFSG.KC.Enum.strictN acc fun a => rep (dg y j) (Gs j) a) m

theorem pc3S_F_succ (z y : ℕ) (Gs : ℕ → ℕ → ℕ) (m : ℕ) :
    pc3S_F z y Gs (m + 1) = rep (dg y m) (Gs m) (pc3S_F z y Gs m) :=
  pc3S_strictN (pc3S_F z y Gs m) (fun a => rep (dg y m) (Gs m) a)

theorem pc3S_rep {Q : ℕ → Prop} {F : ℕ → G} {g : ℕ → ℕ} {h : G}
    (hg : ∀ s, Q s → Q (g s) ∧ F (g s) = F s * h) {e s : ℕ} (he : e < 3) (hs : Q s) :
    Q (rep e g s) ∧ F (rep e g s) = F s * h ^ e := by
  obtain rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  · rw [pc3S_rep_zero, pow_zero, mul_one]
    exact ⟨hs, rfl⟩
  · rw [pc3S_rep_one]
    obtain ⟨a, b⟩ := hg s hs
    exact ⟨a, by rw [b, pow_one]⟩
  · rw [pc3S_rep_two]
    obtain ⟨a, b⟩ := hg s hs
    obtain ⟨c, d⟩ := hg _ a
    exact ⟨c, by rw [d, b, pow_two, mul_assoc]⟩

theorem pc3S_fold {Q : ℕ → Prop} {y z : ℕ} {Gs : ℕ → ℕ → ℕ} {h : ℕ → G} {n : ℕ} (x : ℕ → G)
    (hy : ∀ j, dg y j < 3)
    (hG : ∀ j, dg y j ≠ 0 → ∀ s, Q s → Q (Gs j s) ∧ nv x n (Gs j s) = nv x n s * h j)
    (hz : Q z) :
    ∀ m, Q (pc3S_F z y Gs m) ∧ nv x n (pc3S_F z y Gs m) = nv x n z * pc3nvF h m (dg y)
  | 0 => ⟨hz, by
      change nv x n z = nv x n z * pc3nvF h 0 (dg y)
      simp [pc3nvF]⟩
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := pc3S_fold x hy hG hz m
    rw [pc3S_F_succ, pc3S_nvF_succ]
    by_cases h0 : dg y m = 0
    · rw [h0, pc3S_rep_zero, pow_zero, mul_one]
      exact ⟨ih1, ih2⟩
    · obtain ⟨hQ, hnv⟩ := pc3S_rep (F := nv x n) (hG m h0) (hy m) ih1
      exact ⟨hQ, by rw [hnv, ih2, mul_assoc]⟩

theorem pc3S_mulW (x : ℕ → G) {n y : ℕ} {M : ℕ → ℕ → ℕ} (hy : pc3NW n y)
    (hM : ∀ j, dg y j ≠ 0 → pc3MulOK x n M j) (b : ℕ) (hb : ∀ j, dg y j ≠ 0 → b ≤ j) {s : ℕ}
    (hs : pc3NW n s) :
    pc3NW n (mulW M n s y) ∧ mulW M n s y % 4 ^ b = s % 4 ^ b ∧
      nv x n (mulW M n s y) = nv x n s * nv x n y := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := pc3S_fold (Q := fun r => pc3NW n r ∧ r % 4 ^ b = s % 4 ^ b) (y := y)
    (z := s) (Gs := M) (h := x) x hy.2
    (fun j hj r hr => by
      obtain ⟨a1, a2, a3⟩ := hM j hj r hr.1
      have hdv : 4 ^ b ∣ 4 ^ j := Nat.pow_dvd_pow 4 (hb j hj)
      refine ⟨⟨a1, ?_⟩, a2⟩
      calc M j r % 4 ^ b = M j r % 4 ^ j % 4 ^ b := (Nat.mod_mod_of_dvd _ hdv).symm
        _ = r % 4 ^ j % 4 ^ b := by rw [a3]
        _ = r % 4 ^ b := Nat.mod_mod_of_dvd _ hdv
        _ = s % 4 ^ b := hr.2)
    ⟨hs, rfl⟩ n
  exact ⟨h1, h2, h3⟩

theorem pc3S_conjT {x : ℕ → G} {n CJ k t : ℕ} {M : ℕ → ℕ → ℕ}
    (hCJ : ∀ j < n, k < j → pc3NW n (f32 CJ ((k <<< 4) + j)) ∧
      f32 CJ ((k <<< 4) + j) % 4 ^ (j + 1) = 4 ^ j)
    (hconj : ∀ j < n, k < j → (x k)⁻¹ * x j * x k = nv x n (f32 CJ ((k <<< 4) + j)))
    (ih : ∀ i, k < i → i < n → pc3MulOK x n M i) (ht : pc3NW n t) (htm : t % 4 ^ (k + 1) = 0) :
    pc3NW n (conjT M CJ n k t) ∧ conjT M CJ n k t % 4 ^ (k + 1) = 0 ∧
      nv x n (conjT M CJ n k t) = (x k)⁻¹ * nv x n t * x k := by
  have hkj : ∀ j, dg t j ≠ 0 → k < j ∧ j < n := by
    intro j hj
    refine ⟨?_, pc3S_lt_of_dg ht.1 hj⟩
    by_contra h
    exact hj (pc3S_dg_of_mod htm (by omega))
  obtain ⟨⟨h1, h2⟩, h3⟩ := pc3S_fold (Q := fun r => pc3NW n r ∧ r % 4 ^ (k + 1) = 0) (y := t)
    (z := 0) (Gs := fun j s => mulW M n s (f32 CJ ((k <<< 4) + j)))
    (h := fun j => nv x n (f32 CJ ((k <<< 4) + j))) x ht.2
    (fun j hj s hs => by
      obtain ⟨hkj', hjn⟩ := hkj j hj
      obtain ⟨hcN, hcm⟩ := hCJ j hjn hkj'
      have hcm' : f32 CJ ((k <<< 4) + j) % 4 ^ j = 0 := by
        rw [← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 4 (Nat.le_succ j)), hcm, Nat.mod_self]
      have hpos : ∀ i, dg (f32 CJ ((k <<< 4) + j)) i ≠ 0 → j ≤ i := fun i hi => by
        by_contra h
        exact hi (pc3S_dg_of_mod hcm' (by omega))
      obtain ⟨a1, a2, a3⟩ := pc3S_mulW x hcN
        (fun i hi => ih i (by have := hpos i hi; omega) (pc3S_lt_of_dg hcN.1 hi))
        (k + 1) (fun i hi => by have := hpos i hi; omega) hs.1
      exact ⟨⟨a1, a2.trans hs.2⟩, a3⟩)
    ⟨pc3S_NW_zero, Nat.zero_mod _⟩ n
  have hc : pc3nvF (fun j => nv x n (f32 CJ ((k <<< 4) + j))) n (dg t) =
      pc3nvF (fun j => (x k)⁻¹ * x j * x k) n (dg t) :=
    pc3S_nvF_congr n (fun j _ => by
      by_cases h0 : dg t j = 0
      · simp only [h0, pow_zero]
      · simp only [hconj j (hkj j h0).2 (hkj j h0).1])
  refine ⟨h1, h2, h3.trans ?_⟩
  rw [pc3S_nv_zero, one_mul, hc]
  exact pc3S_nvF_conj x (x k) (dg t) n

theorem pc3S_mulG_succ (PW CJ n f k s : ℕ) : mulG PW CJ n (f + 1) k s =
    Bool.rec (motive := fun _ => ℕ)
      (lowV s k + ((dg s k + 1) <<< (k <<< 1)) + conjT (mulG PW CJ n f) CJ n k (highV s k))
      (lowV s k + mulW (mulG PW CJ n f) n (f32 PW k) (conjT (mulG PW CJ n f) CJ n k (highV s k)))
      (Nat.beq (dg s k) 2) :=
  pc3S_strictN (conjT (mulG PW CJ n f) CJ n k (highV s k)) (fun c =>
    Bool.rec (motive := fun _ => ℕ) (lowV s k + ((dg s k + 1) <<< (k <<< 1)) + c)
      (lowV s k + mulW (mulG PW CJ n f) n (f32 PW k) c) (Nat.beq (dg s k) 2))

theorem pc3S_mulG_two {PW CJ n f k s : ℕ} (h : dg s k = 2) : mulG PW CJ n (f + 1) k s =
    s % 4 ^ k + mulW (mulG PW CJ n f) n (f32 PW k)
      (conjT (mulG PW CJ n f) CJ n k (4 ^ (k + 1) * (s / 4 ^ (k + 1)))) := by
  have hb : Nat.beq (dg s k) 2 = true := by
    rw [Nat.beq_eq]
    exact h
  rw [pc3S_mulG_succ, hb]
  change lowV s k + mulW (mulG PW CJ n f) n (f32 PW k) (conjT (mulG PW CJ n f) CJ n k (highV s k))
    = _
  rw [pc3S_low, pc3S_high]

theorem pc3S_mulG_ne {PW CJ n f k s : ℕ} (h : dg s k ≠ 2) : mulG PW CJ n (f + 1) k s =
    s % 4 ^ k + 4 ^ k * (dg s k + 1) +
      conjT (mulG PW CJ n f) CJ n k (4 ^ (k + 1) * (s / 4 ^ (k + 1))) := by
  have hb : Nat.beq (dg s k) 2 = false := by
    cases hb : Nat.beq (dg s k) 2
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) h
  rw [pc3S_mulG_succ, hb]
  change lowV s k + ((dg s k + 1) <<< (k <<< 1)) + conjT (mulG PW CJ n f) CJ n k (highV s k) = _
  rw [pc3S_low, pc3S_high, Nat.shiftLeft_eq (dg s k + 1) (k <<< 1), pc3S_four_pow,
    Nat.mul_comm (dg s k + 1)]

theorem pc3S_step {x : ℕ → G} {n PW CJ f k : ℕ} (hk : k < n)
    (hPW : pc3NW n (f32 PW k) ∧ f32 PW k % 4 ^ (k + 1) = 0)
    (hCJ : ∀ j < n, k < j → pc3NW n (f32 CJ ((k <<< 4) + j)) ∧
      f32 CJ ((k <<< 4) + j) % 4 ^ (j + 1) = 4 ^ j)
    (hcube : x k ^ 3 = nv x n (f32 PW k))
    (hconj : ∀ j < n, k < j → (x k)⁻¹ * x j * x k = nv x n (f32 CJ ((k <<< 4) + j)))
    (ih : ∀ i, k < i → i < n → pc3MulOK x n (mulG PW CJ n f) i) :
    pc3MulOK x n (mulG PW CJ n (f + 1)) k := by
  intro s hs
  have hpos : 0 < 4 ^ k := by positivity
  have hlowN := (pc3S_NW_split hs k).1
  have htN := (pc3S_NW_split hs (k + 1)).2
  obtain ⟨hcN, hcm, hcv⟩ := pc3S_conjT (x := x) (M := mulG PW CJ n f) hCJ hconj ih htN
    (Nat.mul_mod_right _ _)
  have hdec := pc3S_decomp x s hk
  have he3 := hs.2 k
  by_cases he : dg s k = 2
  · rw [pc3S_mulG_two he]
    generalize conjT (mulG PW CJ n f) CJ n k (4 ^ (k + 1) * (s / 4 ^ (k + 1))) = c
      at hcN hcm hcv ⊢
    have hcpos : ∀ i, dg c i ≠ 0 → k + 1 ≤ i := fun i hi => by
      by_contra hi'
      exact hi (pc3S_dg_of_mod hcm (by omega))
    obtain ⟨hwN, hwm, hwv⟩ := pc3S_mulW x hcN
      (fun i hi => ih i (by have := hcpos i hi; omega) (pc3S_lt_of_dg hcN.1 hi)) (k + 1) hcpos
      hPW.1
    generalize mulW (mulG PW CJ n f) n (f32 PW k) c = w at hwN hwm hwv ⊢
    obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero (hwm.trans hPW.2)
    have hw' : 4 ^ (k + 1) * q = 4 ^ k * (4 * q) := by rw [pow_succ, Nat.mul_assoc]
    rw [hw'] at hwN hwv ⊢
    refine ⟨pc3S_NW_sum hlowN hwN (Nat.mod_lt _ hpos), ?_, ?_⟩
    · rw [pc3S_nvSum x (Nat.mod_lt _ hpos), hwv, ← hcube, hdec, hcv, he, pow_three, pow_two]
      simp only [mul_assoc, mul_inv_cancel_left]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · rw [pc3S_mulG_ne he]
    generalize conjT (mulG PW CJ n f) CJ n k (4 ^ (k + 1) * (s / 4 ^ (k + 1))) = c
      at hcN hcm hcv ⊢
    obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hcm
    have he1 : dg s k + 1 < 3 := by omega
    have ha : s % 4 ^ k + 4 ^ k * (dg s k + 1) < 4 ^ (k + 1) := by
      have := Nat.mod_lt s hpos
      rw [pow_succ]
      nlinarith
    have haN : pc3NW n (s % 4 ^ k + 4 ^ k * (dg s k + 1)) :=
      pc3S_NW_sum hlowN (pc3S_NW_digit hk he1) (Nat.mod_lt _ hpos)
    refine ⟨pc3S_NW_sum haN hcN ha, ?_, ?_⟩
    · rw [pc3S_nvSum x ha, pc3S_nvSum x (Nat.mod_lt _ hpos), pc3S_nv_digit x hk (show dg s k + 1 < 4 by omega), hdec,
        hcv, pow_succ (x k) (dg s k)]
      simp only [mul_assoc, mul_inv_cancel_left]
    · have e : s % 4 ^ k + 4 ^ k * (dg s k + 1) + 4 ^ (k + 1) * q =
          s % 4 ^ k + 4 ^ k * (dg s k + 1 + 4 * q) := by
        rw [pow_succ]
        ring
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem pc3S_mulG_ok {x : ℕ → G} {n PW CJ : ℕ}
    (hPW : ∀ k < n, pc3NW n (f32 PW k) ∧ f32 PW k % 4 ^ (k + 1) = 0)
    (hCJ : ∀ k < n, ∀ j < n, k < j → pc3NW n (f32 CJ ((k <<< 4) + j)) ∧
      f32 CJ ((k <<< 4) + j) % 4 ^ (j + 1) = 4 ^ j)
    (hcube : ∀ k < n, x k ^ 3 = nv x n (f32 PW k))
    (hconj : ∀ k < n, ∀ j < n, k < j → (x k)⁻¹ * x j * x k = nv x n (f32 CJ ((k <<< 4) + j))) :
    ∀ f k, k < n → n - k ≤ f → pc3MulOK x n (mulG PW CJ n f) k
  | 0, _, hk, hf => absurd hf (by omega)
  | f + 1, k, hk, hf => pc3S_step hk (hPW k hk) (hCJ k hk) (hcube k hk) (hconj k hk)
      (fun i hki hi => pc3S_mulG_ok hPW hCJ hcube hconj f i hi (by omega))

theorem pc3S_data {n PW CJ : ℕ} (hd : pcDataOK n PW CJ = true) :
    n ≤ 16 ∧ ∀ k < n, vecOK n (f32 PW k) = true ∧ lowV (f32 PW k) (k + 1) = 0 ∧
      ∀ j < n, k < j → vecOK n (f32 CJ ((k <<< 4) + j)) = true ∧
        lowV (f32 CJ ((k <<< 4) + j)) (j + 1) = 1 <<< (j <<< 1) := by
  obtain ⟨h1, h2⟩ := pc3S_band hd
  refine ⟨Nat.le_of_ble_eq_true h1, fun k hk => ?_⟩
  have h3 := CFSG.KS.PK.allN_iff.1 h2 k hk
  simp only [pc3S_strictB] at h3
  obtain ⟨h4, h5⟩ := pc3S_band h3
  obtain ⟨h6, h7⟩ := pc3S_band h5
  refine ⟨h4, Nat.eq_of_beq_eq_true h6, fun j hj hkj => ?_⟩
  have h8 := pc3S_bif (CFSG.KS.PK.allN_iff.1 h7 j hj) (by rw [Nat.blt_eq]; exact hkj)
  obtain ⟨h9, h10⟩ := pc3S_band h8
  exact ⟨h9, Nat.eq_of_beq_eq_true h10⟩

theorem mulV_sound {x : ℕ → G} {n PW CJ u v : ℕ} (hd : pcDataOK n PW CJ = true)
    (h : PcRel x n PW CJ) (hu : vecOK n u = true) (hv : vecOK n v = true) :
    vecOK n (mulV PW CJ n u v) = true ∧ nv x n (mulV PW CJ n u v) = nv x n u * nv x n v := by
  obtain ⟨hn, H⟩ := pc3S_data hd
  have hV : ∀ w, vecOK n w = true ↔ pc3NW n w := fun w => pc3S_vecOK hn
  have hPW : ∀ k < n, pc3NW n (f32 PW k) ∧ f32 PW k % 4 ^ (k + 1) = 0 := fun k hk =>
    ⟨(hV _).1 (H k hk).1, by rw [← pc3S_low]; exact (H k hk).2.1⟩
  have hCJ : ∀ k < n, ∀ j < n, k < j → pc3NW n (f32 CJ ((k <<< 4) + j)) ∧
      f32 CJ ((k <<< 4) + j) % 4 ^ (j + 1) = 4 ^ j := fun k hk j hj hkj => by
    obtain ⟨a, b⟩ := (H k hk).2.2 j hj hkj
    rw [pc3S_low, Nat.one_shiftLeft, pc3S_four_pow] at b
    exact ⟨(hV _).1 a, b⟩
  have hidx : ∀ k j : ℕ, (k <<< 4) + j = 16 * k + j := fun k j => by
    rw [Nat.shiftLeft_eq]
    ring
  have hok : ∀ k < n, pc3MulOK x n (mulG PW CJ n n) k := fun k hk =>
    pc3S_mulG_ok hPW hCJ h.cube (fun k _ j hj hkj => by rw [hidx]; exact h.conj k j hkj hj) n k
      hk (Nat.sub_le n k)
  have hvN := (hV v).1 hv
  obtain ⟨h1, -, h3⟩ := pc3S_mulW x hvN (fun j hj => hok j (pc3S_lt_of_dg hvN.1 hj)) 0
    (fun j _ => Nat.zero_le j) ((hV u).1 hu)
  exact ⟨(hV _).2 h1, h3⟩

end CFSG.KS.Pc3

end
