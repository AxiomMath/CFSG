module

public import Certificates.Data.Kernel.TcRes.C2Plane
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

namespace CFSG.KC.TcRes.Lane

open CFSG.TcRes.TK

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nsub (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nmod (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
theorem npow (a b : ℕ) : Nat.pow a b = a ^ b := rfl
theorem nland (a b : ℕ) : Nat.land a b = a &&& b := rfl
theorem nlor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem nshr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
theorem nshl (a b : ℕ) : Nat.shiftLeft a b = a <<< b := rfl
theorem nxor (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_eq_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem allLt_succ (c : ℕ) (p : ℕ → Bool) : allLt (c + 1) p = andB (p c) (allLt c p) := rfl

theorem allLt_iff {c : ℕ} {p : ℕ → Bool} : allLt c p = true ↔ ∀ m < c, p m = true := by
  induction c with
  | zero => simp [allLt]
  | succ c ih =>
    rw [allLt_succ, andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ m hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
      · exact h2 m h
      · exact h1
    · intro h
      exact ⟨h c (Nat.lt_succ_self c), fun m hm => h m (Nat.lt_succ_of_lt hm)⟩

theorem anyLt_iff {c : ℕ} {p : ℕ → Bool} : anyLt c p = true ↔ ∃ m < c, p m = true := by
  induction c with
  | zero => simp [anyLt]
  | succ c ih =>
    rw [show anyLt (c + 1) p = orB (p c) (anyLt c p) from rfl, orB_eq_true, ih]
    constructor
    · rintro (h | ⟨m, hm, h⟩)
      · exact ⟨c, Nat.lt_succ_self c, h⟩
      · exact ⟨m, Nat.lt_succ_of_lt hm, h⟩
    · rintro ⟨m, hm, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h' | rfl
      · exact Or.inr ⟨m, h', h⟩
      · exact Or.inl h

theorem sumLt_eq (c : ℕ) (f : ℕ → ℕ) : sumLt c f = ∑ i ∈ Finset.range c, f i := by
  induction c with
  | zero => rfl
  | succ c ih =>
    rw [Finset.sum_range_succ, ← ih]
    change strictN (sumLt c f) (fun a => a + f c) = _
    rw [strictN_eq]

theorem beq_eq_true {a b : ℕ} : Nat.beq a b = true ↔ a = b := Nat.beq_eq_true_eq a b ▸ Iff.rfl

theorem beq_eq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_eq_true]

theorem blt_eq_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by
  simp [Nat.blt_eq]

theorem bit_iff {m i : ℕ} : bit m i = true ↔ m.testBit i = true := by
  change Nat.blt 0 (m &&& (1 <<< i)) = true ↔ _
  rw [blt_eq_true, Nat.shiftLeft_eq, one_mul, Nat.pos_iff_ne_zero]
  constructor
  · intro h
    by_contra hb
    apply h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : i = j
    · subst hj
      simpa using hb
    · simp [hj]
  · intro h h0
    have := congrArg (fun t => t.testBit i) h0
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, h, Bool.and_true,
      Nat.zero_testBit] at this
    exact absurd this (by decide)

theorem ble_eq_true {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := by
  simp [Nat.ble_eq]

theorem boolRec_nat (x y : ℕ) (b : Bool) :
    Bool.rec (motive := fun _ => ℕ) x y b = if b = true then y else x := by
  cases b <;> rfl

theorem b2n_eq (b : Bool) : b2n b = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem fld_eq (t w i : ℕ) : fld t w i = t / 2 ^ (w * i) % 2 ^ w := by
  change t >>> (w * i) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem fld_lt (t w i : ℕ) : fld t w i < 2 ^ w := by
  rw [fld_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos w)

theorem testBit_fld (t w i j : ℕ) :
    (fld t w i).testBit j = (decide (j < w) && t.testBit (w * i + j)) := by
  rw [fld_eq, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j]

theorem fld_land (a b w i : ℕ) : fld (a &&& b) w i = fld a w i &&& fld b w i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_fld, Nat.testBit_and]
  cases decide (j < w) <;> simp

theorem fld_zero (w i : ℕ) : fld 0 w i = 0 := by
  simp [fld_eq]

theorem fld_shr (t w s m : ℕ) : fld (t >>> (w * s)) w m = fld t w (s + m) := by
  rw [fld_eq, fld_eq, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add, mul_add]

theorem fld_fld (t w L i m : ℕ) (hm : m < L) :
    fld (fld t (w * L) i) w m = fld t w (L * i + m) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_fld]
  by_cases hj : j < w
  · have h1 : w * m + j < w * L :=
      calc w * m + j < w * m + w := by omega
        _ = w * (m + 1) := by ring
        _ ≤ w * L := Nat.mul_le_mul_left _ hm
    simp only [hj, h1, decide_true, Bool.true_and]
    congr 1
    ring
  · simp [hj]

theorem sum_lanes_lt (w K : ℕ) (c : ℕ → ℕ) (hc : ∀ k < K, c k < 2 ^ w) :
    ∑ k ∈ Finset.range K, c k * 2 ^ (w * k) < 2 ^ (w * K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih fun k hk => hc k (by omega)
    have h2 : c K + 1 ≤ 2 ^ w := hc K (by omega)
    calc _ < 2 ^ (w * K) + c K * 2 ^ (w * K) := Nat.add_lt_add_right h1 _
      _ = (c K + 1) * 2 ^ (w * K) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * K) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (w * (K + 1)) := by rw [← pow_add]; ring_nf

theorem fld_sum_lanes (w K : ℕ) (c : ℕ → ℕ) (hc : ∀ k < K, c k < 2 ^ w) (j : ℕ) :
    fld (∑ k ∈ Finset.range K, c k * 2 ^ (w * k)) w j = if j < K then c j else 0 := by
  induction K with
  | zero => simp [fld_zero]
  | succ K ih =>
    have hc' : ∀ k < K, c k < 2 ^ w := fun k hk => hc k (by omega)
    have h1 := sum_lanes_lt w K c hc'
    rcases lt_trichotomy j K with hj | rfl | hj
    · obtain ⟨d, hd⟩ : ∃ d, K = j + 1 + d := ⟨K - j - 1, by omega⟩
      have e : c K * 2 ^ (w * K) = 2 ^ (w * j) * (2 ^ w * (c K * 2 ^ (w * d))) := by
        rw [hd]
        ring
      rw [Finset.sum_range_succ, fld_eq, e, Nat.add_mul_div_left _ _ (by positivity),
        Nat.add_mul_mod_self_left, ← fld_eq, ih hc']
      simp [hj, show j < K + 1 by omega]
    · rw [Finset.sum_range_succ, fld_eq, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt h1, zero_add, Nat.mod_eq_of_lt (hc j (by omega))]
      simp
    · have h2 := sum_lanes_lt w (K + 1) c hc
      rw [fld_eq, Nat.div_eq_of_lt (lt_of_lt_of_le h2
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w (by omega))))]
      simp [show ¬ j < K + 1 by omega]

theorem eq_sum_lanes (w K z : ℕ) (hz : z < 2 ^ (w * K)) :
    z = ∑ k ∈ Finset.range K, fld z w k * 2 ^ (w * k) := by
  suffices h : ∀ K, z % 2 ^ (w * K) = ∑ k ∈ Finset.range K, fld z w k * 2 ^ (w * k) by
    rw [← h K, Nat.mod_eq_of_lt hz]
  intro K
  induction K with
  | zero => simp [Nat.mod_one]
  | succ K ih =>
    rw [Finset.sum_range_succ, ← ih, fld_eq, mul_add, mul_one, pow_add, Nat.mod_mul]
    ring

theorem fld_eq_zero_of_lt (w K z : ℕ) (hz : z < 2 ^ (w * K)) {j : ℕ} (hj : K ≤ j) :
    fld z w j = 0 := by
  rw [fld_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hz
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hj))), Nat.zero_mod]

theorem lanes_eq_of_eq (w K : ℕ) {c d : ℕ → ℕ} (hc : ∀ k < K, c k < 2 ^ w)
    (hd : ∀ k < K, d k < 2 ^ w)
    (h : ∑ k ∈ Finset.range K, c k * 2 ^ (w * k) = ∑ k ∈ Finset.range K, d k * 2 ^ (w * k))
    {k : ℕ} (hk : k < K) : c k = d k := by
  have h1 := fld_sum_lanes w K c hc k
  rw [h, fld_sum_lanes w K d hd k, if_pos hk, if_pos hk] at h1
  exact h1.symm

theorem ones_eq (n : ℕ) : ones n = ∑ k ∈ Finset.range n, 1 * 2 ^ (16 * k) := by
  have h : ∀ n, 65535 * (∑ k ∈ Finset.range n, 1 * 2 ^ (16 * k)) + 1 = 2 ^ (16 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, mul_add, mul_one, pow_add]
      ring
  change ((1 <<< (16 * n)) - 1) / 65535 = _
  rw [Nat.shiftLeft_eq, one_mul, ← h n, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num)]

theorem fld_mul_ones (c n m : ℕ) (hc : c < 2 ^ 16) (hm : m < n) : fld (c * ones n) 16 m = c := by
  rw [ones_eq, Finset.mul_sum]
  simp_rw [← mul_assoc, mul_one]
  rw [fld_sum_lanes 16 n (fun _ => c) (fun _ _ => hc), if_pos hm]

theorem fld_land_eq_zero {z c n m : ℕ} (h : z &&& (c * ones n) = 0) (hc : c < 2 ^ 16)
    (hm : m < n) : fld z 16 m &&& c = 0 := by
  have h1 := congrArg (fun t => fld t 16 m) h
  simp only [fld_land, fld_zero, fld_mul_ones c n m hc hm] at h1
  exact h1

theorem lt_of_land_eq_zero {x c b : ℕ} (hx : x < 2 ^ 16) (hb : b ≤ 16)
    (hc : ∀ i, b ≤ i → i < 16 → c.testBit i = true) (h : x &&& c = 0) : x < 2 ^ b := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases h16 : i < 16
  · have h1 := congrArg (fun t => t.testBit i) h
    simp only [Nat.testBit_and, hc i hi h16, Bool.and_true, Nat.zero_testBit] at h1
    exact h1
  · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem fld_mul (w A B x y : ℕ) (hx : x < 2 ^ (w * A)) (hy : y < 2 ^ (w * B))
    (hc : ∀ k, ∑ i ∈ Finset.range (k + 1), fld x w i * fld y w (k - i) < 2 ^ w) (k : ℕ) :
    fld (x * y) w k = ∑ i ∈ Finset.range (k + 1), fld x w i * fld y w (k - i) := by
  classical
  set conv := fun k => ∑ i ∈ Finset.range (k + 1), fld x w i * fld y w (k - i) with hconv
  have hz : ∀ k, A + B ≤ k → conv k = 0 := by
    intro k hk
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rcases lt_or_ge i A with h | h
    · rw [fld_eq_zero_of_lt w B y hy (by omega), mul_zero]
    · rw [fld_eq_zero_of_lt w A x hx h, zero_mul]
  let P : Polynomial ℕ := ∑ a ∈ Finset.range A, Polynomial.C (fld x w a) * Polynomial.X ^ a
  let Q : Polynomial ℕ := ∑ a ∈ Finset.range B, Polynomial.C (fld y w a) * Polynomial.X ^ a
  have hPc : ∀ i, P.coeff i = fld x w i := by
    intro i
    simp only [P, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range A) i (fun a => fld x w a)]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range] at h
      exact (fld_eq_zero_of_lt w A x hx (by omega)).symm
  have hQc : ∀ i, Q.coeff i = fld y w i := by
    intro i
    simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range B) i (fun a => fld y w a)]
    split_ifs with h
    · rfl
    · rw [Finset.mem_range] at h
      exact (fld_eq_zero_of_lt w B y hy (by omega)).symm
  have hPe : P.eval (2 ^ w) = x := by
    simp only [P, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
    exact (eq_sum_lanes w A x hx).symm
  have hQe : Q.eval (2 ^ w) = y := by
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, ← pow_mul]
    exact (eq_sum_lanes w B y hy).symm
  have hPQc : ∀ k, (P * Q).coeff k = conv k := by
    intro k
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => P.coeff i * Q.coeff j)]
    simp only [hPc, hQc, hconv]
  have hdeg : (P * Q).natDegree < A + B + 1 := by
    rw [Nat.lt_succ_iff, Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hPQc]
    exact hz N (by exact_mod_cast hN.le)
  have hxy : x * y = ∑ k ∈ Finset.range (A + B + 1), conv k * 2 ^ (w * k) := by
    rw [← hPe, ← hQe, ← Polynomial.eval_mul, Polynomial.eval_eq_sum_range' hdeg]
    simp only [hPQc, ← pow_mul]
  rw [hxy, fld_sum_lanes w _ conv (fun k _ => hc k)]
  split_ifs with h
  · rfl
  · exact (hz k (by omega)).symm

theorem conv_le (w L x y X0 Y0 : ℕ) (hx : x < 2 ^ (w * L)) (hxl : ∀ i, fld x w i ≤ X0)
    (hyl : ∀ i, fld y w i ≤ Y0) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), fld x w i * fld y w (k - i) ≤ L * (X0 * Y0) := by
  classical
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), if i < L then X0 * Y0 else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with h
        · exact Nat.mul_le_mul (hxl i) (hyl _)
        · rw [fld_eq_zero_of_lt w L x hx (by omega), zero_mul]
    _ = ((Finset.range (k + 1)).filter (· < L)).card * (X0 * Y0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
    _ ≤ L * (X0 * Y0) := by
        apply Nat.mul_le_mul_right
        calc _ ≤ (Finset.range L).card := Finset.card_le_card (fun i hi => by
              simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
              exact hi.2)
          _ = L := Finset.card_range L

theorem dP_eq (n pr : ℕ) : dP n pr = fld pr 16 (n - 1) + fld pr 16 (3 * n - 1) := rfl

theorem dQ_eq (n pr : ℕ) : dQ n pr = fld pr 16 (2 * n - 1) := rfl

theorem dPQ {n x y : ℕ} (hn1 : 1 ≤ n) (hn8 : n ≤ 8) (hx : x < 2 ^ (16 * (2 * n)))
    (hy : y < 2 ^ (16 * (2 * n))) (hxl : ∀ i, fld x 16 i ≤ 7) (hyl : ∀ i, fld y 16 i ≤ 3) :
    ((dP n (x * y) : ℤ) - dQ n (x * y) = ∑ a ∈ Finset.range n,
      ((fld x 16 a : ℤ) - fld x 16 (n + a)) *
        ((fld y 16 (n - 1 - a) : ℤ) - fld y 16 (2 * n - 1 - a))) ∧
    dP n (x * y) ≤ 672 ∧ dQ n (x * y) ≤ 336 := by
  have hb : ∀ k, ∑ i ∈ Finset.range (k + 1), fld x 16 i * fld y 16 (k - i) ≤ 336 := fun k =>
    (conv_le 16 (2 * n) x y 7 3 hx hxl hyl k).trans (by omega)
  have hm := fld_mul 16 (2 * n) (2 * n) x y hx hy (fun k => lt_of_le_of_lt (hb k) (by norm_num))
  have hy0 : ∀ i, 2 * n ≤ i → fld y 16 i = 0 := fun i hi => fld_eq_zero_of_lt 16 (2 * n) y hy hi
  have hx0 : ∀ i, 2 * n ≤ i → fld x 16 i = 0 := fun i hi => fld_eq_zero_of_lt 16 (2 * n) x hx hi
  refine ⟨?_, ?_, ?_⟩
  · rw [dP_eq, dQ_eq, hm, hm, hm]
    have e1 : n - 1 + 1 = n := by omega
    have e2 : 2 * n - 1 + 1 = n + n := by omega
    have e3 : 3 * n - 1 + 1 = n + n + n := by omega
    rw [e1, e2, e3]
    simp only [Finset.sum_range_add]
    have s1 : ∑ i ∈ Finset.range n, fld x 16 i * fld y 16 (3 * n - 1 - i) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [Finset.mem_range] at hi
        rw [hy0 _ (by omega), mul_zero]
    have s3 : ∑ i ∈ Finset.range n, fld x 16 (n + n + i) * fld y 16 (3 * n - 1 - (n + n + i)) =
        0 := Finset.sum_eq_zero fun i _ => by rw [hx0 _ (by omega), zero_mul]
    have s2 : ∑ i ∈ Finset.range n, fld x 16 (n + i) * fld y 16 (3 * n - 1 - (n + i)) =
        ∑ i ∈ Finset.range n, fld x 16 (n + i) * fld y 16 (2 * n - 1 - i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [Finset.mem_range] at hi
        congr 2
        omega
    have s4 : ∑ i ∈ Finset.range n, fld x 16 (n + i) * fld y 16 (2 * n - 1 - (n + i)) =
        ∑ i ∈ Finset.range n, fld x 16 (n + i) * fld y 16 (n - 1 - i) :=
      Finset.sum_congr rfl fun i hi => by
        rw [Finset.mem_range] at hi
        congr 2
        omega
    rw [s1, s3, s2, s4]
    push_cast
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  · rw [dP_eq, hm, hm]
    have := hb (n - 1)
    have := hb (3 * n - 1)
    omega
  · rw [dQ_eq, hm]
    exact hb _

theorem add_lanes (L a b : ℕ) (ha : a < 2 ^ (16 * L)) (hb : b < 2 ^ (16 * L)) :
    a + b = ∑ k ∈ Finset.range L, (fld a 16 k + fld b 16 k) * 2 ^ (16 * k) := by
  conv_lhs => rw [eq_sum_lanes 16 L a ha, eq_sum_lanes 16 L b hb]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (add_mul _ _ _).symm

theorem mul_ones (c n : ℕ) : c * ones n = ∑ k ∈ Finset.range n, c * 2 ^ (16 * k) := by
  rw [ones_eq, Finset.mul_sum]
  simp_rw [one_mul]

theorem fld_add {L a b m : ℕ} (ha : a < 2 ^ (16 * L)) (hb : b < 2 ^ (16 * L))
    (hc : ∀ k < L, fld a 16 k + fld b 16 k < 2 ^ 16) (hm : m < L) :
    fld (a + b) 16 m = fld a 16 m + fld b 16 m := by
  rw [add_lanes L a b ha hb, fld_sum_lanes 16 L _ hc, if_pos hm]

theorem lanes_lin {n A A' B c c' d d' : ℕ} (hA : A < 2 ^ (16 * n)) (hA' : A' < 2 ^ (16 * n))
    (hB : B < 2 ^ (16 * n)) (h1 : ∀ k < n, fld A 16 k + c * fld B 16 k + d < 2 ^ 16)
    (h2 : ∀ k < n, fld A' 16 k + c' * fld B 16 k + d' < 2 ^ 16)
    (h : A + c * B + d * ones n = A' + c' * B + d' * ones n) {k : ℕ} (hk : k < n) :
    fld A 16 k + c * fld B 16 k + d = fld A' 16 k + c' * fld B 16 k + d' := by
  have e : ∀ A c d : ℕ, A < 2 ^ (16 * n) → A + c * B + d * ones n =
      ∑ k ∈ Finset.range n, (fld A 16 k + c * fld B 16 k + d) * 2 ^ (16 * k) := by
    intro A c d hA
    conv_lhs => rw [eq_sum_lanes 16 n A hA, eq_sum_lanes 16 n B hB, mul_ones, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e A c d hA, e A' c' d' hA'] at h
  exact lanes_eq_of_eq 16 n h1 h2 h hk

theorem fld_two_pow {n i m : ℕ} (hi : i < n) :
    fld (1 <<< (16 * i)) 16 m = if m = i then 1 else 0 := by
  classical
  have e : 1 <<< (16 * i) = ∑ k ∈ Finset.range n, (if k = i then 1 else 0) * 2 ^ (16 * k) := by
    rw [Nat.shiftLeft_eq, one_mul]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, if_pos hi]
  rw [e, fld_sum_lanes 16 n _ (fun k _ => by split_ifs <;> norm_num)]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

theorem lt_pow_of_lt_mul {a b c : ℕ} (h : a < 2 ^ (b * (2 * c))) : a >>> (b * c) < 2 ^ (b * c) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
  convert h using 2
  ring

theorem srtWalk_succ (N W K V SRT c s prev : ℕ) : srtWalk N W K V SRT (c + 1) s prev =
    andB (andB (Nat.blt (fld SRT W s) N) (Nat.blt prev (fld V K (fld SRT W s))))
      (srtWalk N W K V SRT c (s + 1) (fld V K (fld SRT W s))) := by
  simp only [srtWalk, strictB_eq]

theorem srtWalk_spec (N W K V SRT : ℕ) : ∀ c s prev, srtWalk N W K V SRT c s prev = true →
    (∀ t < c, fld SRT W (s + t) < N) ∧ (∀ t < c, prev < fld V K (fld SRT W (s + t))) ∧
    ∀ t t', t < t' → t' < c → fld V K (fld SRT W (s + t)) < fld V K (fld SRT W (s + t')) := by
  intro c
  induction c with
  | zero => intro s prev _; exact ⟨fun t h => absurd h (Nat.not_lt_zero _),
      fun t h => absurd h (Nat.not_lt_zero _), fun t t' _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ c ih =>
    intro s prev h
    rw [srtWalk_succ, andB_eq_true, andB_eq_true, blt_eq_true, blt_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨i1, i2, i3⟩ := ih _ _ h3
    have hs : ∀ t, s + 1 + t = s + (t + 1) := fun t => by omega
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t t' htt ht' => ?_⟩
    · rcases t with _ | t
      · simpa using h1
      · rw [← hs]
        exact i1 t (by omega)
    · rcases t with _ | t
      · simpa using h2
      · rw [← hs]
        exact h2.trans (i2 t (by omega))
    · obtain ⟨t', rfl⟩ : ∃ u, t' = u + 1 := ⟨t' - 1, by omega⟩
      rw [← hs]
      rcases t with _ | t
      · simpa using i2 t' (by omega)
      · rw [← hs]
        exact i3 t t' (by omega) (by omega)

theorem fld_one_eq_one {x v : ℕ} : fld x 1 v = 1 ↔ x.testBit v = true := by
  have h := testBit_fld x 1 v 0
  simp only [zero_lt_one, decide_true, Bool.true_and, add_zero, one_mul] at h
  rw [← h]
  have hl := fld_lt x 1 v
  rcases (by omega : fld x 1 v = 0 ∨ fld x 1 v = 1) with h0 | h0 <;> rw [h0] <;> decide

section Wide

variable {w K : ℕ}

theorem lowW_eq (w K : ℕ) (hw : 1 ≤ w) : lowW w K = ∑ k ∈ Finset.range K, 1 * 2 ^ (w * k) := by
  have h : ∀ K, (2 ^ w - 1) * (∑ k ∈ Finset.range K, 1 * 2 ^ (w * k)) + 1 = 2 ^ (w * K) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, add_right_comm, ih, one_mul, mul_add, mul_one, pow_add]
      have : 1 ≤ 2 ^ w := Nat.one_le_two_pow
      zify [this]
      ring
  have hp : 0 < 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    omega
  change ((1 <<< (w * K)) - 1) / ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul, ← h K, Nat.add_sub_cancel,
    Nat.mul_div_cancel_left _ hp]

theorem low_lt (hw : 1 ≤ w) (K : ℕ) : lowW w K < 2 ^ (w * K) := by
  rw [lowW_eq w K hw]
  exact sum_lanes_lt w K _ (fun _ _ => Nat.one_lt_two_pow (by omega))

theorem fld_mul_low (hw : 1 ≤ w) {c k : ℕ} (hc : c < 2 ^ w) (hk : k < K) :
    fld (c * lowW w K) w k = c := by
  rw [lowW_eq w K hw, Finset.mul_sum]
  simp_rw [← mul_assoc, mul_one]
  rw [fld_sum_lanes w K (fun _ => c) (fun _ _ => hc), if_pos hk]

theorem mul_low_lt (hw : 1 ≤ w) {c : ℕ} (hc : c < 2 ^ w) : c * lowW w K < 2 ^ (w * K) := by
  rw [lowW_eq w K hw, Finset.mul_sum]
  simp_rw [← mul_assoc, mul_one]
  exact sum_lanes_lt w K _ (fun _ _ => hc)

theorem fld_add_w {a b k : ℕ} (ha : a < 2 ^ (w * K)) (hb : b < 2 ^ (w * K))
    (hc : ∀ k < K, fld a w k + fld b w k < 2 ^ w) (hk : k < K) :
    fld (a + b) w k = fld a w k + fld b w k ∧ a + b < 2 ^ (w * K) := by
  have e : a + b = ∑ k ∈ Finset.range K, (fld a w k + fld b w k) * 2 ^ (w * k) := by
    conv_lhs => rw [eq_sum_lanes w K a ha, eq_sum_lanes w K b hb]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (add_mul _ _ _).symm
  rw [e, fld_sum_lanes w K _ hc, if_pos hk]
  exact ⟨rfl, sum_lanes_lt w K _ hc⟩

theorem fld_sub_low (hw : 1 ≤ w) {z c k : ℕ} (hz : z < 2 ^ (w * K)) (hc : c < 2 ^ w)
    (hle : ∀ k < K, c ≤ fld z w k) (hk : k < K) :
    fld (z - c * lowW w K) w k = fld z w k - c ∧ z - c * lowW w K < 2 ^ (w * K) := by
  have hl : ∀ k < K, fld z w k - c < 2 ^ w := fun k _ => lt_of_le_of_lt (Nat.sub_le _ _)
    (fld_lt _ _ _)
  have e : z - c * lowW w K = ∑ k ∈ Finset.range K, (fld z w k - c) * 2 ^ (w * k) := by
    have e2 : z = ∑ k ∈ Finset.range K, (fld z w k - c) * 2 ^ (w * k) + c * lowW w K := by
      conv_lhs => rw [eq_sum_lanes w K z hz]
      rw [lowW_eq w K hw, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have := hle k (Finset.mem_range.1 hk)
      rw [one_mul, ← add_mul, Nat.sub_add_cancel this]
    omega
  rw [e, fld_sum_lanes w K _ hl, if_pos hk]
  exact ⟨rfl, sum_lanes_lt w K _ hl⟩

theorem fld_shr_div {y s k : ℕ} (hy : y < 2 ^ (w * K)) (hd : ∀ k < K, 2 ^ s ∣ fld y w k)
    (hk : k < K) : fld (y >>> s) w k = fld y w k / 2 ^ s ∧ y >>> s < 2 ^ (w * K) := by
  have hl : ∀ k < K, fld y w k / 2 ^ s < 2 ^ w := fun k _ =>
    lt_of_le_of_lt (Nat.div_le_self _ _) (fld_lt _ _ _)
  have e : y >>> s = ∑ k ∈ Finset.range K, (fld y w k / 2 ^ s) * 2 ^ (w * k) := by
    rw [Nat.shiftRight_eq_div_pow]
    conv_lhs => rw [eq_sum_lanes w K y hy]
    rw [Nat.div_eq_iff_eq_mul_left (by positivity) (Finset.dvd_sum fun k hk =>
      Dvd.dvd.mul_right (hd k (Finset.mem_range.1 hk)) _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mul_right_comm, Nat.div_mul_cancel (hd k (Finset.mem_range.1 hk))]
  rw [e, fld_sum_lanes w K _ hl, if_pos hk]
  exact ⟨rfl, sum_lanes_lt w K _ hl⟩

theorem fld_lor (a b w i : ℕ) : fld (a ||| b) w i = fld a w i ||| fld b w i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_fld, Nat.testBit_or]
  cases decide (j < w) <;> simp

theorem fld_xor (a b w i : ℕ) : fld (a ^^^ b) w i = fld a w i ^^^ fld b w i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_fld, Nat.testBit_xor]
  cases decide (j < w) <;> simp

theorem fld_shr3_low (hw : 4 ≤ w) {y k : ℕ} (hk : k < K) :
    fld ((y >>> 3) &&& lowW w K) w k = fld y w k / 8 % 2 := by
  have h1 : fld (lowW w K) w k = 1 := by
    have := fld_mul_low (K := K) (by omega : 1 ≤ w) (Nat.one_lt_two_pow (by omega : w ≠ 0)) hk
    rwa [one_mul] at this
  have e8 : 2 ^ w = 8 * 2 ^ (w - 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
    congr 1
    omega
  have h2 : 2 ∣ 2 ^ (w - 3) := dvd_pow_self 2 (by omega)
  rw [fld_land, h1, Nat.and_one_is_mod, fld_eq, fld_eq, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega)), e8,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ h2, Nat.div_div_eq_div_mul, mul_comm (2 ^ 3)]

theorem fld_mod {z k : ℕ} (hk : k < K) : fld (z % 2 ^ (w * K)) w k = fld z w k := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_fld, Nat.testBit_mod_two_pow]
  by_cases hj : j < w
  · have : w * k + j < w * K :=
      calc w * k + j < w * k + w := by omega
        _ = w * (k + 1) := by ring
        _ ≤ w * K := Nat.mul_le_mul_left _ hk
    simp [hj, this]
  · simp [hj]

theorem land_mod {x y n : ℕ} (hy : y < 2 ^ n) : x &&& y = (x % 2 ^ n) &&& y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < n
  · simp [hi]
  · have : y.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [this]

theorem fld_add_low {a b u : ℕ} (hc : ∀ k ≤ u, fld a w k + fld b w k < 2 ^ w) :
    fld (a + b) w u = fld a w u + fld b w u := by
  have hu : u < u + 1 := Nat.lt_succ_self u
  have hc' : ∀ k < u + 1, fld (a % 2 ^ (w * (u + 1))) w k + fld (b % 2 ^ (w * (u + 1))) w k <
      2 ^ w := fun k hk => by
    rw [fld_mod hk, fld_mod hk]
    exact hc k (by omega)
  have ha := Nat.mod_lt a (Nat.two_pow_pos (w * (u + 1)))
  have hb := Nat.mod_lt b (Nat.two_pow_pos (w * (u + 1)))
  obtain ⟨h1, h2⟩ := fld_add_w ha hb hc' hu
  rw [← fld_mod (K := u + 1) hu, Nat.add_mod, Nat.mod_eq_of_lt h2, h1, fld_mod hu, fld_mod hu]

theorem fld_smul_low {a c u : ℕ} (hc : ∀ k ≤ u, c * fld a w k < 2 ^ w) :
    fld (c * a) w u = c * fld a w u := by
  have hu : u < u + 1 := Nat.lt_succ_self u
  have ha := Nat.mod_lt a (Nat.two_pow_pos (w * (u + 1)))
  have e : c * (a % 2 ^ (w * (u + 1))) =
      ∑ k ∈ Finset.range (u + 1), (c * fld a w k) * 2 ^ (w * k) := by
    conv_lhs => rw [eq_sum_lanes w (u + 1) _ ha]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [fld_mod (Finset.mem_range.1 hk)]
    ring
  have hc' : ∀ k < u + 1, c * fld a w k < 2 ^ w := fun k hk => hc k (by omega)
  have hlt : c * (a % 2 ^ (w * (u + 1))) < 2 ^ (w * (u + 1)) := by
    rw [e]
    exact sum_lanes_lt w _ _ hc'
  have e2 : c * a = c * (a % 2 ^ (w * (u + 1))) +
      2 ^ (w * (u + 1)) * (c * (a / 2 ^ (w * (u + 1)))) := by
    conv_lhs => rw [← Nat.mod_add_div a (2 ^ (w * (u + 1)))]
    ring
  rw [← fld_mod (K := u + 1) hu, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, e,
    fld_sum_lanes w _ _ hc', if_pos hu]

theorem fld_zl (hw : 5 ≤ w) {x k : ℕ} (hx : x < 2 ^ (w * K)) (hxl : ∀ k < K, fld x w k ≤ 28)
    (hk : k < K) : fld (zl (lowW w K) x) w k = if fld x w k % 3 = 0 then 1 else 0 := by
  have hw1 : 1 ≤ w := by omega
  have h32 : 32 ≤ 2 ^ w := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  have hc : ∀ c, c < 32 → c < 2 ^ w := fun c h => lt_of_lt_of_le h h32
  have hA : ∀ x, x < 2 ^ (w * K) → (x &&& 3 * lowW w K) < 2 ^ (w * K) ∧
      ∀ k < K, fld (x &&& 3 * lowW w K) w k = fld x w k % 4 := by
    intro x hx
    refine ⟨lt_of_le_of_lt Nat.and_le_left hx, fun k hk => ?_⟩
    rw [fld_land, fld_mul_low hw1 (hc 3 (by norm_num)) hk]
    exact Nat.and_two_pow_sub_one_eq_mod _ 2
  have hB : ∀ x, x < 2 ^ (w * K) → (∀ k < K, fld x w k < 32) →
      (x &&& 28 * lowW w K) >>> 2 < 2 ^ (w * K) ∧
      ∀ k < K, fld ((x &&& 28 * lowW w K) >>> 2) w k = fld x w k / 4 := by
    intro x hx hxl
    have hy : x &&& 28 * lowW w K < 2 ^ (w * K) := lt_of_le_of_lt Nat.and_le_left hx
    have hl : ∀ k < K, fld (x &&& 28 * lowW w K) w k = fld x w k &&& 28 := fun k hk => by
      rw [fld_land, fld_mul_low hw1 (hc 28 (by norm_num)) hk]
    have hd : ∀ k < K, 2 ^ 2 ∣ fld (x &&& 28 * lowW w K) w k := fun k hk => by
      rw [hl k hk]
      have := hxl k hk
      generalize fld x w k = a at this ⊢
      interval_cases a <;> decide
    refine ⟨lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) hy,
      fun k hk => ?_⟩
    rw [(fld_shr_div hy hd hk).1, hl k hk]
    have := hxl k hk
    generalize fld x w k = a at this ⊢
    interval_cases a <;> decide
  have hS : ∀ y, y < 2 ^ (w * K) → (∀ k < K, fld y w k < 32) →
      (y &&& (3 * lowW w K)) + ((y &&& (28 * lowW w K)) >>> 2) < 2 ^ (w * K) ∧
      ∀ k < K, fld ((y &&& (3 * lowW w K)) + ((y &&& (28 * lowW w K)) >>> 2)) w k =
        fld y w k % 4 + fld y w k / 4 := by
    intro y hy hyl
    obtain ⟨a1, a2⟩ := hA y hy
    obtain ⟨b1, b2⟩ := hB y hy hyl
    have hc' : ∀ k < K, fld (y &&& (3 * lowW w K)) w k +
        fld ((y &&& (28 * lowW w K)) >>> 2) w k < 2 ^ w := fun k hk => by
      rw [a2 k hk, b2 k hk]
      have := hyl k hk
      have : fld y w k % 4 + fld y w k / 4 < 32 := by omega
      exact hc _ this
    refine ⟨?_, fun k hk => ?_⟩
    · rcases Nat.eq_zero_or_pos K with h0 | h0
      · subst h0
        simp only [mul_zero, pow_zero, Nat.lt_one_iff] at a1 b1 ⊢
        rw [a1, b1]
      · exact (fld_add_w a1 b1 hc' h0).2
    · rw [(fld_add_w a1 b1 hc' hk).1, a2 k hk, b2 k hk]
  have hxl32 : ∀ k < K, fld x w k < 32 := fun k hk => by have := hxl k hk; omega
  obtain ⟨s1, s2⟩ := hS x hx hxl32
  set x1 := (x &&& (3 * lowW w K)) + ((x &&& (28 * lowW w K)) >>> 2) with hx1
  have hx1l : ∀ k < K, fld x1 w k < 32 := fun k hk => by
    rw [s2 k hk]
    have := hxl k hk
    omega
  obtain ⟨t1, t2⟩ := hS x1 s1 hx1l
  set z0 := (x1 &&& (3 * lowW w K)) + ((x1 &&& (28 * lowW w K)) >>> 2) with hz0
  have h8 : 8 * lowW w K < 2 ^ (w * K) := mul_low_lt hw1 (hc 8 (by norm_num))
  have hzc : ∀ k < K, fld z0 w k + fld (8 * lowW w K) w k < 2 ^ w := fun k hk => by
    rw [t2 k hk, s2 k hk, fld_mul_low hw1 (hc 8 (by norm_num)) hk]
    have := hxl k hk
    have : (fld x w k % 4 + fld x w k / 4) % 4 + (fld x w k % 4 + fld x w k / 4) / 4 + 8 < 32 := by
      omega
    exact hc _ this
  have hz : ∀ k < K, fld (z0 + 8 * lowW w K) w k =
      (fld x w k % 4 + fld x w k / 4) % 4 + (fld x w k % 4 + fld x w k / 4) / 4 + 8 := by
    intro k hk
    rw [(fld_add_w t1 h8 hzc hk).1, t2 k hk, s2 k hk, fld_mul_low hw1 (hc 8 (by norm_num)) hk]
  have hzb : z0 + 8 * lowW w K < 2 ^ (w * K) := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      simp only [mul_zero, pow_zero, Nat.lt_one_iff] at t1 h8 ⊢
      rw [t1, h8]
    · exact (fld_add_w t1 h8 hzc h0).2
  have hE : ∀ c, c ≤ 4 → ∀ k < K, fld (((z0 + 8 * lowW w K) - c * lowW w K) >>> 3 &&& lowW w K) w k
      = (fld (z0 + 8 * lowW w K) w k - c) / 8 % 2 := by
    intro c hc4 k hk
    rw [fld_shr3_low (by omega) hk, (fld_sub_low hw1 hzb (hc c (by omega)) (fun k hk => by
      rw [hz k hk]
      omega) hk).1]
  have hL : fld (lowW w K) w k = 1 := by
    have := fld_mul_low (K := K) hw1 (Nat.one_lt_two_pow (by omega : w ≠ 0)) hk
    rwa [one_mul] at this
  simp only [zl, strictN_eq, nadd, nmul, nland, nshr, nsub, nlor, nxor,
    show ∀ c, lowW w K * c = c * lowW w K from fun c => mul_comm _ _]
  rw [← hx1, ← hz0]
  have e1 := hE 1 (by norm_num) k hk
  have e3 := hE 3 (by norm_num) k hk
  have e4 := hE 4 (by norm_num) k hk
  rw [one_mul] at e1
  rw [fld_lor, fld_xor, e1, fld_land, e3, fld_xor, e4, hL, hz k hk]
  have := hxl k hk
  generalize fld x w k = a at this ⊢
  interval_cases a <;> decide

theorem fld_zl_any (hw : 5 ≤ w) {x k : ℕ} (hxl : ∀ k < K, fld x w k ≤ 28) (hk : k < K) :
    fld (zl (lowW w K) x) w k = if fld x w k % 3 = 0 then 1 else 0 := by
  have hc : ∀ c, c < 32 → lowW w K * c < 2 ^ (w * K) := fun c h => by
    rw [mul_comm]
    exact mul_low_lt (by omega) (lt_of_lt_of_le h (by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw))
  have e : zl (lowW w K) x = zl (lowW w K) (x % 2 ^ (w * K)) := by
    simp only [zl, strictN_eq, nmul, nland]
    rw [land_mod (x := x) (hc 3 (by norm_num)), land_mod (x := x) (hc 28 (by norm_num))]
  rw [e, fld_zl hw (Nat.mod_lt _ (Nat.two_pow_pos _)) (fun k hk => by rw [fld_mod hk]; exact hxl k hk)
    hk, fld_mod hk]

end Wide

theorem boolRec_true {a b c : Bool} :
    Bool.rec (motive := fun _ => Bool) a b c = true ↔ (c = true → b = true) ∧ (c = false → a = true) := by
  cases c <;> simp

end CFSG.KC.TcRes.Lane

end
