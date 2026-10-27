module

public import Certificates.Data.Kernel.B433Alt.Om
public import CFSG.Certificates.Kernel.BenesSound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.B433Alt

open CFSG.KC.B4A CFSG.KC.Y333 CFSG.KC.Benes

theorem omS_sN (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

@[expose] def omS_bsum (s : ℕ) (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => omS_bsum s b n + if b n then 2 ^ (s * n) else 0

theorem omS_bsum_lt {s : ℕ} (hs : 0 < s) (b : ℕ → Bool) : ∀ n, omS_bsum s b n < 2 ^ (s * n)
  | 0 => by simp [omS_bsum]
  | n + 1 => by
    have ih := omS_bsum_lt hs b n
    have h2 : 2 ^ (s * n) * 2 ≤ 2 ^ (s * (n + 1)) := by
      rw [show s * (n + 1) = s * n + s by ring, Nat.pow_add]
      exact Nat.mul_le_mul_left _ (by
        have := Nat.pow_le_pow_right (n := 2) (by decide) hs
        simpa using this)
    have h3 : (if b n then 2 ^ (s * n) else 0) ≤ 2 ^ (s * n) := by split <;> omega
    show omS_bsum s b n + (if b n then 2 ^ (s * n) else 0) < _
    omega

theorem omS_testBit_bsum {s : ℕ} (hs : 0 < s) (b : ℕ → Bool) : ∀ n p,
    (omS_bsum s b n).testBit p = (decide (p < s * n ∧ p % s = 0) && b (p / s))
  | 0, p => by simp [omS_bsum]
  | n + 1, p => by
    have ih := omS_testBit_bsum hs b n
    have hlt := omS_bsum_lt hs b n
    have e : omS_bsum s b (n + 1) = 2 ^ (s * n) * (if b n then 1 else 0) + omS_bsum s b n := by
      show omS_bsum s b n + (if b n then 2 ^ (s * n) else 0) = _
      split <;> simp [Nat.add_comm]
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    have hdm := Nat.div_add_mod p s
    have hms := Nat.mod_lt p hs
    by_cases hp : p < s * n
    · rw [if_pos hp, ih p]
      have : p < s * (n + 1) := lt_of_lt_of_le hp (Nat.mul_le_mul_left _ (by omega))
      simp only [hp, this, true_and]
    · rw [if_neg hp]
      have hn : n ≤ p / s := (Nat.le_div_iff_mul_le hs).2 (by rw [Nat.mul_comm]; omega)
      by_cases he : p = s * n
      · subst he
        rw [Nat.sub_self, Nat.mul_div_cancel_left _ hs, Nat.mul_mod_right]
        have : s * n < s * (n + 1) := Nat.mul_lt_mul_of_pos_left (by omega) hs
        cases b n <;> simp [this]
      · have h1 : p - s * n ≠ 0 := by omega
        have h2 : ¬ (p < s * (n + 1) ∧ p % s = 0) := by
          rintro ⟨h3, h4⟩
          have h5 : p / s < n + 1 := (Nat.div_lt_iff_lt_mul hs).2 (by rw [Nat.mul_comm]; exact h3)
          have h6 : p / s = n := by omega
          rw [h6, h4] at hdm
          omega
        rw [decide_eq_false h2, Bool.false_and]
        cases b n
        · simp
        · simp only [if_true]
          rw [Nat.testBit_lt_two_pow (x := 1) (i := p - s * n)
            (Nat.one_lt_two_pow (by omega))]

theorem omS_bsum_congr {s : ℕ} {b b' : ℕ → Bool} : ∀ n, (∀ k < n, b k = b' k) →
    omS_bsum s b n = omS_bsum s b' n
  | 0, _ => rfl
  | n + 1, h => by
    show omS_bsum s b n + _ = omS_bsum s b' n + _
    rw [omS_bsum_congr n (fun k hk => h k (by omega)), h n (by omega)]

@[expose] noncomputable def omS_mlo (k : ℕ) : ℕ := 2 ^ (64 * k) * magic20 % 2 ^ 1216

@[expose] noncomputable def omS_mhi (k : ℕ) : ℕ := 2 ^ (64 * k) * magic20 / 2 ^ 1216 / 2 ^ 64

@[expose] noncomputable def omS_loSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => omS_loSum n + omS_mlo n

theorem omS_magic_mid : ∀ k < 20, 2 ^ (64 * k) * magic20 / 2 ^ 1216 % 2 ^ 64 = 2 ^ k := by
  decide +kernel

theorem omS_loSum_lt : omS_loSum 20 < 2 ^ 1216 := by decide +kernel

theorem omS_str20_eq : str20 = omS_bsum 64 (fun _ => true) 20 := by decide +kernel

theorem omS_magic_split {k : ℕ} (hk : k < 20) :
    2 ^ (64 * k) * magic20 = omS_mlo k + 2 ^ 1216 * (2 ^ k + 2 ^ 64 * omS_mhi k) := by
  have h1 := Nat.mod_add_div (2 ^ (64 * k) * magic20) (2 ^ 1216)
  have h2 := Nat.mod_add_div (2 ^ (64 * k) * magic20 / 2 ^ 1216) (2 ^ 64)
  rw [omS_magic_mid k hk] at h2
  rw [omS_mlo, omS_mhi]
  conv_lhs => rw [← h1, ← h2]

theorem omS_bsum_mul_magic (b : ℕ → Bool) : ∀ n ≤ 20, ∃ lo hi, lo ≤ omS_loSum n ∧
    omS_bsum 64 b n * magic20 = lo + 2 ^ 1216 * (omS_bsum 1 b n + 2 ^ 64 * hi)
  | 0, _ => ⟨0, 0, le_rfl, by
    rw [show omS_bsum 64 b 0 = 0 from rfl, show omS_bsum 1 b 0 = 0 from rfl, Nat.zero_mul,
      Nat.mul_zero, Nat.add_zero, Nat.mul_zero, Nat.add_zero]⟩
  | n + 1, hn => by
    obtain ⟨lo, hi, hlo, e⟩ := omS_bsum_mul_magic b n (by omega)
    have hs := omS_magic_split (k := n) (by omega)
    show ∃ lo hi, lo ≤ omS_loSum n + omS_mlo n ∧
      (omS_bsum 64 b n + if b n then 2 ^ (64 * n) else 0) * magic20 =
        lo + 2 ^ 1216 * ((omS_bsum 1 b n + if b n then 2 ^ (1 * n) else 0) + 2 ^ 64 * hi)
    cases b n
    · refine ⟨lo, hi, by omega, ?_⟩
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      exact e
    · refine ⟨lo + omS_mlo n, hi + omS_mhi n, by omega, ?_⟩
      simp only [if_true, Nat.one_mul]
      rw [Nat.add_mul, e, hs]
      generalize (2 : ℕ) ^ 1216 = K
      ring

theorem omS_gather {i lo S hi : ℕ} (hlo : lo < 2 ^ i) (hS : S < 2 ^ 20) :
    Nat.land (Nat.shiftRight (lo + 2 ^ i * (S + 2 ^ 64 * hi)) i) (2 ^ 20 - 1) = S := by
  rw [nland, nshr, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos i),
    Nat.div_eq_of_lt hlo, Nat.zero_add, Nat.and_two_pow_sub_one_eq_mod,
    show (2 : ℕ) ^ 64 = 2 ^ 20 * 2 ^ 44 by norm_num, Nat.mul_assoc, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hS]

theorem omS_colGet_eq (B o : ℕ) :
    colGet B o = omS_bsum 1 (fun k => B.testBit (o + 64 * k)) 20 := by
  have hv : Nat.land (Nat.shiftRight B o) str20 =
      omS_bsum 64 (fun k => B.testBit (o + 64 * k)) 20 := by
    apply Nat.eq_of_testBit_eq
    intro p
    rw [nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, omS_str20_eq,
      omS_testBit_bsum (by decide), omS_testBit_bsum (by decide)]
    by_cases h : p < 64 * 20 ∧ p % 64 = 0
    · rw [decide_eq_true h, Bool.true_and, Bool.true_and, Bool.and_true]
      congr 2
      omega
    · rw [decide_eq_false h, Bool.false_and, Bool.false_and, Bool.and_false]
  obtain ⟨lo, hi, hlo, e⟩ := omS_bsum_mul_magic (fun k => B.testBit (o + 64 * k)) 20 le_rfl
  have hlo' : lo < 2 ^ 1216 := lt_of_le_of_lt hlo omS_loSum_lt
  have hS := omS_bsum_lt (s := 1) (by decide) (fun k => B.testBit (o + 64 * k)) 20
  unfold colGet
  rw [hv, nmul, e]
  exact omS_gather (i := 1216) hlo' hS

theorem omS_testBit_untag (B p : ℕ) :
    (untag B).testBit p = (decide (p < 81920) && B.testBit p) := by
  have h : ∀ n, (B &&& (1 <<< n - 1)).testBit p = (decide (p < n) && B.testBit p) := by
    intro n
    rw [Nat.one_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_comm]
  exact h 81920

theorem omS_testBit_catTree (f : ℕ → ℕ) : ∀ k b p, (catTree f k b).testBit p =
    (decide (p < 81920 * 2 ^ k) && (f (b + p / 81920)).testBit (p % 81920))
  | 0, b, p => by
    rw [show catTree f 0 b = untag (f b) from rfl, omS_testBit_untag, pow_zero, Nat.mul_one]
    by_cases hp : p < 81920
    · rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, Nat.add_zero]
    · rw [decide_eq_false hp, Bool.false_and, Bool.false_and]
  | k + 1, b, p => by
    rw [show catTree f (k + 1) b =
      cat (81920 * 2 ^ k) (catTree f k b) (catTree f k (b + 2 ^ k)) from rfl]
    unfold cat
    rw [nlor, nshl, Nat.testBit_or, Nat.testBit_shiftLeft, omS_testBit_catTree f k b p,
      omS_testBit_catTree f k (b + 2 ^ k)]
    have h2 : 81920 * 2 ^ (k + 1) = 81920 * 2 ^ k + 81920 * 2 ^ k := by rw [Nat.pow_succ]; ring
    by_cases hp : p < 81920 * 2 ^ k
    · rw [decide_eq_true hp, decide_eq_false (show ¬ p ≥ 81920 * 2 ^ k by omega),
        decide_eq_true (show p < 81920 * 2 ^ (k + 1) by omega)]
      simp only [Bool.true_and, Bool.false_and, Bool.or_false]
    · obtain ⟨p', rfl⟩ : ∃ p', p = 81920 * 2 ^ k + p' := ⟨p - 81920 * 2 ^ k, by omega⟩
      have e1 : (81920 * 2 ^ k + p') / 81920 = 2 ^ k + p' / 81920 :=
        Nat.mul_add_div (by norm_num) _ _
      have e2 : (81920 * 2 ^ k + p') % 81920 = p' % 81920 := Nat.mul_add_mod _ _ _
      rw [decide_eq_false hp, decide_eq_true (show 81920 * 2 ^ k + p' ≥ 81920 * 2 ^ k by omega),
        Nat.add_sub_cancel_left, Bool.false_and, Bool.false_or, Bool.true_and, e1, e2,
        Nat.add_assoc]
      congr 1
      exact decide_eq_decide.2 (by omega)

theorem omS_rep2_mul {P : ℕ} (hP : 0 < P) : ∀ m, (2 ^ P - 1) * rep2 P m = 2 ^ (P * 2 ^ m) - 1
  | 0 => by
    show (2 ^ P - 1) * 1 = 2 ^ (P * 2 ^ 0) - 1
    rw [pow_zero, Nat.mul_one, Nat.mul_one]
  | m + 1 => by
    have ih := omS_rep2_mul hP m
    have hA : 1 ≤ 2 ^ P - 1 := by have := Nat.one_lt_two_pow (n := P) (by omega); omega
    have hr : rep2 P m < 2 ^ (P * 2 ^ m) := by
      have h1 : rep2 P m ≤ (2 ^ P - 1) * rep2 P m := Nat.le_mul_of_pos_left _ (by omega)
      have h2 := Nat.two_pow_pos (P * 2 ^ m)
      omega
    have e : rep2 P (m + 1) = 2 ^ (P * 2 ^ m) * rep2 P m + rep2 P m := by
      show Nat.lor (rep2 P m) (Nat.shiftLeft (rep2 P m) (Nat.mul P (Nat.shiftLeft 1 m))) = _
      simp only [nlor, nshl, nmul, Nat.one_shiftLeft]
      rw [Nat.shiftLeft_eq, Nat.lor_comm, Nat.mul_comm (rep2 P m),
        ← Nat.two_pow_add_eq_or_of_lt hr]
    have hpos := Nat.two_pow_pos (P * 2 ^ m)
    rw [e, show P * 2 ^ (m + 1) = P * 2 ^ m + P * 2 ^ m by rw [Nat.pow_succ]; ring, Nat.pow_add]
    generalize 2 ^ (P * 2 ^ m) = A at ih hr hpos ⊢
    generalize 2 ^ P - 1 = c at ih hA ⊢
    obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm c, Nat.mul_assoc, ih, Nat.add_sub_cancel]
    have : (a + 1) * (a + 1) = (a + 1) * a + a + 1 := by ring
    omega

theorem omS_rep2_eq {P : ℕ} (hP : 0 < P) (m : ℕ) :
    rep2 P m = (2 ^ (P * 2 ^ m) - 1) / (2 ^ P - 1) := by
  rw [← omS_rep2_mul hP m, Nat.mul_div_cancel_left _
    (by have := Nat.one_lt_two_pow (n := P) (by omega); omega)]

theorem omS_testBit_rep2_mul {P c : ℕ} (hP : 0 < P) (hc : c < 2 ^ P) (m q : ℕ) :
    (rep2 P m * c).testBit q = (decide (q < P * 2 ^ m) && c.testBit (q % P)) := by
  rw [omS_rep2_eq hP, Nat.mul_comm]
  exact testBit_mul_div hP rfl hc q

@[expose] noncomputable def omS_Mj (m j : ℕ) : ℕ :=
  rep2 (1280 * (2 * 2 ^ j)) (m - 1 - j) * ((2 ^ (64 * 2 ^ j) - 1) * 2 ^ (1280 * 2 ^ j))

theorem omS_unStepM_eq (m x j : ℕ) :
    unStepM m x j = (x ^^^ (x &&& omS_Mj m j)) ||| ((x &&& omS_Mj m j) >>> (1216 * 2 ^ j)) := by
  unfold unStepM omS_Mj
  simp only [nlor, nxor, nland, nshr, nmul, nshl, nsub, Nat.shiftLeft_eq, Nat.one_mul]

theorem omS_testBit_Mj (m j t : ℕ) : (omS_Mj m j).testBit t =
    (decide (t < 2 * (1280 * 2 ^ j) * 2 ^ (m - 1 - j)) &&
      (decide (1280 * 2 ^ j ≤ t % (2 * (1280 * 2 ^ j))) &&
        decide (t % (2 * (1280 * 2 ^ j)) - 1280 * 2 ^ j < 64 * 2 ^ j))) := by
  unfold omS_Mj
  have hP : 0 < 1280 * (2 * 2 ^ j) := by positivity
  have hc : (2 ^ (64 * 2 ^ j) - 1) * 2 ^ (1280 * 2 ^ j) < 2 ^ (1280 * (2 * 2 ^ j)) := by
    calc (2 ^ (64 * 2 ^ j) - 1) * 2 ^ (1280 * 2 ^ j) < 2 ^ (64 * 2 ^ j) * 2 ^ (1280 * 2 ^ j) :=
          Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
            (Nat.two_pow_pos _)
      _ = 2 ^ (64 * 2 ^ j + 1280 * 2 ^ j) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ (1280 * (2 * 2 ^ j)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [omS_testBit_rep2_mul hP hc, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    show 1280 * (2 * 2 ^ j) = 2 * (1280 * 2 ^ j) by ring]

@[expose] def omS_UInv (m j : ℕ) (T : ℕ → Bool) (x : ℕ) : Prop :=
  ∀ q, x.testBit q = (decide (q % (1280 * 2 ^ j) < 64 * 2 ^ j ∧ q / (1280 * 2 ^ j) < 2 ^ (m - j)) &&
    T (64 * 2 ^ j * (q / (1280 * 2 ^ j)) + q % (1280 * 2 ^ j)))

theorem omS_dm {M a r : ℕ} (hr : r < M) : (M * a + r) / M = a ∧ (M * a + r) % M = r := by
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem omS_uinv_zero (m k C : ℕ) :
    omS_UInv m 0 (fun y => C.testBit (64 * k + 1280 * (y / 64) + y % 64))
      ((C >>> (64 * k)) &&& (rep2 1280 m * (2 ^ 64 - 1))) := by
  intro q
  have hc : 2 ^ 64 - 1 < 2 ^ 1280 := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) (show 64 ≤ 1280 by norm_num)
    have := Nat.two_pow_pos 64
    omega
  rw [Nat.testBit_and, Nat.testBit_shiftRight, omS_testBit_rep2_mul (by norm_num) hc,
    Nat.testBit_two_pow_sub_one]
  simp only [pow_zero, Nat.mul_one, Nat.sub_zero]
  have e4 : q < 1280 * 2 ^ m ↔ q / 1280 < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num), Nat.mul_comm]
  by_cases h : q % 1280 < 64
  · have e1 : (64 * (q / 1280) + q % 1280) / 64 = q / 1280 := by omega
    have e2 : (64 * (q / 1280) + q % 1280) % 64 = q % 1280 := by omega
    have e3 : 64 * k + 1280 * (q / 1280) + q % 1280 = 64 * k + q := by omega
    rw [e1, e2, e3, decide_eq_true h, Bool.and_true]
    by_cases h2 : q / 1280 < 2 ^ m
    · rw [decide_eq_true (e4.2 h2), decide_eq_true (show q % 1280 < 64 ∧ q / 1280 < 2 ^ m from
        ⟨h, h2⟩), Bool.and_true, Bool.true_and]
    · rw [decide_eq_false (mt e4.1 h2), decide_eq_false (show ¬ (q % 1280 < 64 ∧ q / 1280 < 2 ^ m)
        from fun h3 => h2 h3.2), Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h, Bool.and_false, Bool.and_false,
      decide_eq_false (show ¬ (q % 1280 < 64 ∧ q / 1280 < 2 ^ m) from fun h3 => h h3.1),
      Bool.false_and]

theorem omS_uinv_succ {m j : ℕ} {T : ℕ → Bool} {x : ℕ} (hj : j < m) (hx : omS_UInv m j T x) :
    omS_UInv m (j + 1) T (unStepM m x j) := by
  intro q
  rw [omS_unStepM_eq, Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_and, omS_testBit_Mj, omS_testBit_Mj]
  have hG2 : 64 * 2 ^ (j + 1) = 2 * (64 * 2 ^ j) := by rw [Nat.pow_succ]; ring
  have hL2 : 1280 * 2 ^ (j + 1) = 2 * (1280 * 2 ^ j) := by rw [Nat.pow_succ]; ring
  have hS : 1216 * 2 ^ j = 1280 * 2 ^ j - 64 * 2 ^ j := by omega
  have hP2 : 2 ^ (m - j) = 2 * 2 ^ (m - 1 - j) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hP1 : 2 ^ (m - (j + 1)) = 2 ^ (m - 1 - j) := by
    congr 1
    omega
  rw [hG2, hL2, hP1, hS, hx, hx, hP2]
  have hG0 : 0 < 64 * 2 ^ j := by positivity
  have hLG : 1280 * 2 ^ j = 20 * (64 * 2 ^ j) := by ring
  generalize 64 * 2 ^ j = G at hG0 hLG ⊢
  generalize 1280 * 2 ^ j = L at hLG ⊢
  generalize 2 ^ (m - 1 - j) = P
  subst hLG
  obtain ⟨a, β, hβ, rfl⟩ : ∃ a β, β < 2 * (20 * G) ∧ q = 2 * (20 * G) * a + β :=
    ⟨q / (2 * (20 * G)), q % (2 * (20 * G)), Nat.mod_lt _ (by omega),
      (Nat.div_add_mod q (2 * (20 * G))).symm⟩
  obtain ⟨d0, m0⟩ := omS_dm (M := 2 * (20 * G)) (a := a) hβ
  rw [d0, m0]
  have hr1 : ∀ γ, γ < 2 * (20 * G) →
      (2 * (20 * G) * a + γ < 2 * (20 * G) * P ↔ a < P) := by
    intro γ hγ
    constructor
    · intro h
      by_contra hc
      have : 2 * (20 * G) * P ≤ 2 * (20 * G) * a := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro h
      have : 2 * (20 * G) * (a + 1) ≤ 2 * (20 * G) * P := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at this
      omega
  simp only [hr1 β hβ]
  have hT : G * (2 * a) + β = 2 * G * a + β := by ring
  rcases Nat.lt_or_ge β G with h1 | h1
  ·
    have e1 : 2 * (20 * G) * a + β = 20 * G * (2 * a) + β := by ring
    obtain ⟨d1, m1⟩ := omS_dm (M := 20 * G) (a := 2 * a) (r := β) (by omega)
    have e2 : 20 * G - G + (2 * (20 * G) * a + β) = 2 * (20 * G) * a + (20 * G - G + β) := by
      omega
    obtain ⟨d2, m2⟩ := omS_dm (M := 2 * (20 * G)) (a := a) (r := 20 * G - G + β) (by omega)
    have e3 : 20 * G - G + (2 * (20 * G) * a + β) = 20 * G * (2 * a) + (20 * G - G + β) := by
      omega
    obtain ⟨d3, m3⟩ := omS_dm (M := 20 * G) (a := 2 * a) (r := 20 * G - G + β) (by omega)
    rw [e1, d1, m1, ← e1, e2, m2, ← e2, e3, d3, m3, ← e3, hT,
      decide_eq_false (show ¬ (20 * G ≤ β) by omega),
      decide_eq_false (show ¬ (20 * G ≤ 20 * G - G + β) by omega)]
    simp only [Bool.false_and, Bool.and_false, Bool.xor_false, Bool.or_false]
    have ha2 : 2 * a < 2 * P ↔ a < P := by omega
    by_cases ha : a < P
    · rw [decide_eq_true (show β < G ∧ 2 * a < 2 * P from ⟨h1, ha2.2 ha⟩),
        decide_eq_true (show β < 2 * G ∧ a < P from ⟨by omega, ha⟩)]
    · rw [decide_eq_false (show ¬ (β < G ∧ 2 * a < 2 * P) from fun h => ha (ha2.1 h.2)),
        decide_eq_false (show ¬ (β < 2 * G ∧ a < P) from fun h => ha h.2)]
  · rcases Nat.lt_or_ge β (20 * G) with h2 | h2
    ·
      have e1 : 2 * (20 * G) * a + β = 20 * G * (2 * a) + β := by ring
      obtain ⟨d1, m1⟩ := omS_dm (M := 20 * G) (a := 2 * a) (r := β) (by omega)
      have e2 : 20 * G - G + (2 * (20 * G) * a + β) = 2 * (20 * G) * a + (20 * G - G + β) := by
        omega
      obtain ⟨d2, m2⟩ := omS_dm (M := 2 * (20 * G)) (a := a) (r := 20 * G - G + β) (by omega)
      have e3 : 20 * G - G + (2 * (20 * G) * a + β) = 20 * G * (2 * a + 1) + (β - G) := by
        have : 20 * G * (2 * a + 1) = 2 * (20 * G) * a + 20 * G := by ring
        omega
      obtain ⟨d3, m3⟩ := omS_dm (M := 20 * G) (a := 2 * a + 1) (r := β - G) (by omega)
      have hT2 : G * (2 * a + 1) + (β - G) = 2 * G * a + β := by
        have : G * (2 * a + 1) = 2 * G * a + G := by ring
        omega
      rw [e1, d1, m1, ← e1, e2, m2]
      simp only [hr1 (20 * G - G + β) (by omega)]
      rw [← e2, e3, d3, m3, hT2,
        decide_eq_false (show ¬ (β < G ∧ 2 * a < 2 * P) by omega),
        decide_eq_true (show 20 * G ≤ 20 * G - G + β by omega),
        show 20 * G - G + β - 20 * G = β - G by omega]
      simp only [Bool.false_and, Bool.false_xor, Bool.false_or, Bool.true_and]
      have ha2 : 2 * a + 1 < 2 * P ↔ a < P := by omega
      by_cases ha : a < P
      · by_cases hb : β < 2 * G
        · rw [decide_eq_true (show β - G < G ∧ 2 * a + 1 < 2 * P from ⟨by omega, ha2.2 ha⟩),
            decide_eq_true ha, decide_eq_true (show β - G < G by omega),
            decide_eq_true (show β < 2 * G ∧ a < P from ⟨hb, ha⟩)]
          simp
        · rw [decide_eq_false (show ¬ (β - G < G ∧ 2 * a + 1 < 2 * P) by omega),
            decide_eq_false (show ¬ (β < 2 * G ∧ a < P) by omega)]
          simp
      · rw [decide_eq_false (show ¬ (β - G < G ∧ 2 * a + 1 < 2 * P) by omega),
          decide_eq_false (show ¬ (β < 2 * G ∧ a < P) by omega)]
        simp
    ·
      have e1 : 2 * (20 * G) * a + β = 20 * G * (2 * a + 1) + (β - 20 * G) := by
        have : 20 * G * (2 * a + 1) = 2 * (20 * G) * a + 20 * G := by ring
        omega
      obtain ⟨d1, m1⟩ := omS_dm (M := 20 * G) (a := 2 * a + 1) (r := β - 20 * G) (by omega)
      have hfirst : ((decide ((2 * (20 * G) * a + β) % (20 * G) < G ∧
            (2 * (20 * G) * a + β) / (20 * G) < 2 * P) &&
          T (G * ((2 * (20 * G) * a + β) / (20 * G)) + (2 * (20 * G) * a + β) % (20 * G))) ^^
        ((decide ((2 * (20 * G) * a + β) % (20 * G) < G ∧
            (2 * (20 * G) * a + β) / (20 * G) < 2 * P) &&
          T (G * ((2 * (20 * G) * a + β) / (20 * G)) + (2 * (20 * G) * a + β) % (20 * G))) &&
          (decide (a < P) && (decide (20 * G ≤ β) && decide (β - 20 * G < G))))) = false := by
        rw [e1, d1, m1]
        by_cases hc : β - 20 * G < G ∧ 2 * a + 1 < 2 * P
        · rw [decide_eq_true hc, decide_eq_true (show a < P by omega),
            decide_eq_true (show 20 * G ≤ β by omega), decide_eq_true hc.1]
          simp
        · rw [decide_eq_false hc]
          simp
      rw [hfirst, Bool.false_or, decide_eq_false (show ¬ (β < 2 * G ∧ a < P) by omega),
        Bool.false_and]
      have hmask : (decide (20 * G - G + (2 * (20 * G) * a + β) < 2 * (20 * G) * P) &&
          (decide (20 * G ≤ (20 * G - G + (2 * (20 * G) * a + β)) % (2 * (20 * G))) &&
            decide ((20 * G - G + (2 * (20 * G) * a + β)) % (2 * (20 * G)) - 20 * G < G))) =
          false := by
        rcases Nat.lt_or_ge β (20 * G + G) with h3 | h3
        · have e2 : 20 * G - G + (2 * (20 * G) * a + β) =
              2 * (20 * G) * a + (20 * G - G + β) := by omega
          obtain ⟨-, m2⟩ := omS_dm (M := 2 * (20 * G)) (a := a) (r := 20 * G - G + β) (by omega)
          rw [e2, m2, decide_eq_false (show ¬ (20 * G - G + β - 20 * G < G) by omega)]
          simp
        · have e2 : 20 * G - G + (2 * (20 * G) * a + β) =
              2 * (20 * G) * (a + 1) + (β - 20 * G - G) := by
            have : 2 * (20 * G) * (a + 1) = 2 * (20 * G) * a + 2 * (20 * G) := by ring
            omega
          obtain ⟨-, m2⟩ := omS_dm (M := 2 * (20 * G)) (a := a + 1) (r := β - 20 * G - G)
            (by omega)
          rw [e2, m2, decide_eq_false (show ¬ (20 * G ≤ β - 20 * G - G) by omega)]
          simp
      rw [hmask, Bool.and_false]

theorem omS_testBit_unspreadM (m C k q : ℕ) : (unspreadM m C k).testBit q =
    (decide (q < 64 * 2 ^ m) && C.testBit (64 * k + 1280 * (q / 64) + q % 64)) := by
  have key : ∀ j, j ≤ m → omS_UInv m j (fun y => C.testBit (64 * k + 1280 * (y / 64) + y % 64))
      (Nat.rec (motive := fun _ => ℕ) ((C >>> (64 * k)) &&& (rep2 1280 m * (2 ^ 64 - 1)))
        (fun j x => unStepM m x j) j) := by
    intro j
    induction j with
    | zero => intro _; exact omS_uinv_zero m k C
    | succ j ih => intro hj; exact omS_uinv_succ (by omega) (ih (by omega))
  have e : unspreadM m C k = Nat.rec (motive := fun _ => ℕ)
      ((C >>> (64 * k)) &&& (rep2 1280 m * (2 ^ 64 - 1))) (fun j x => unStepM m x j) m := rfl
  rw [e, key m le_rfl q, Nat.sub_self, pow_zero]
  by_cases hq : q < 64 * 2 ^ m
  · have hq' : q < 1280 * 2 ^ m := by omega
    rw [Nat.div_eq_of_lt hq', Nat.mod_eq_of_lt hq', Nat.mul_zero, Nat.zero_add,
      decide_eq_true hq, decide_eq_true (show q < 64 * 2 ^ m ∧ 0 < 1 from ⟨hq, by omega⟩)]
  · have : ¬ (q % (1280 * 2 ^ m) < 64 * 2 ^ m ∧ q / (1280 * 2 ^ m) < 1) := by
      rintro ⟨h1, h2⟩
      have h0 : q / (1280 * 2 ^ m) = 0 := Nat.lt_one_iff.1 h2
      have := Nat.div_add_mod q (1280 * 2 ^ m)
      rw [h0, Nat.mul_zero, Nat.zero_add] at this
      omega
    rw [decide_eq_false this, decide_eq_false hq, Bool.false_and, Bool.false_and]

theorem omS_colOff (y : ℕ) : colOff y = 1280 * (y / 64 % 64) + y % 64 := by
  show 1280 * ((y >>> 6) &&& (2 ^ 6 - 1)) + (y &&& (2 ^ 6 - 1)) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem omS_testBit_colPlane (CB : ℕ → ℕ) (c b : ℕ) {y : ℕ} (hy : y < 2 ^ 19) (hb : b < 20) :
    (colPlane CB c b).testBit y = (CB (256 * c + y / 4096)).testBit (colOff y + 64 * b) := by
  have e : colPlane CB c b = unspreadM 13 (catTree (fun x => CB (256 * c + x)) 7 0) b := rfl
  rw [e, omS_testBit_unspreadM, omS_testBit_catTree, omS_colOff]
  have hy' : y < 64 * 2 ^ 13 := by norm_num; omega
  have hp : 64 * b + 1280 * (y / 64) + y % 64 < 81920 * 2 ^ 7 := by norm_num; omega
  have e1 : (64 * b + 1280 * (y / 64) + y % 64) / 81920 = y / 4096 := by omega
  have e2 : (64 * b + 1280 * (y / 64) + y % 64) % 81920 =
      1280 * (y / 64 % 64) + y % 64 + 64 * b := by
    omega
  rw [decide_eq_true hy', Bool.true_and, decide_eq_true hp, Bool.true_and, Nat.zero_add, e1, e2]

theorem omS_sN_tag {v x R : ℕ} {T : ℕ → ℕ → Bool} (ht : T v x = true)
    (h : colGet v (colOff x) = R) :
    sN v (fun B => Bool.rec (motive := fun _ => ℕ) (nat_lit 1048576) (colGet B (colOff x))
      (T B x)) = R := by
  rw [omS_sN]
  show Bool.rec (motive := fun _ => ℕ) (nat_lit 1048576) (colGet v (colOff x)) (T v x) = R
  rw [ht]
  exact h

theorem omS_colAt_eq {CB : ℕ → ℕ} {c x : ℕ} (hx : x < 2 ^ 19)
    (htag : CB (256 * c + x / 4096) >>> 81920 = x / 4096) :
    colAt CB c x = omS_bsum 1 (fun k => (colPlane CB c k).testBit x) 20 := by
  have hidx : Nat.add (Nat.mul 256 c) (Nat.shiftRight x 12) = 256 * c + x / 4096 := by
    rw [nadd, nmul, nshr, Nat.shiftRight_eq_div_pow]
  have ht : tagOK (CB (256 * c + x / 4096)) x = true := by
    unfold tagOK
    rw [nshr, nshr, htag, Nat.shiftRight_eq_div_pow]
    exact Nat.beq_refl _
  unfold colAt
  rw [hidx]
  refine omS_sN_tag (T := tagOK) ht ?_
  rw [omS_colGet_eq]
  exact omS_bsum_congr 20 fun k hk => (omS_testBit_colPlane CB c k hx hk).symm

end CFSG.KC.B433Alt

end
