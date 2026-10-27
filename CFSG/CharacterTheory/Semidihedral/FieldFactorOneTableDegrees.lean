module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

open Finset

namespace CFSG.Semidihedral.FieldFactorOne

@[expose] def orderFourValue (k : ℕ) (Lm : ℕ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range (4 * k),
    (if j % 4 = 0 then Lm j else if j % 4 = 2 then -Lm j else 0)

namespace DegreeCongruences

theorem sum_range_four_mul (f : ℕ → ℤ) (k : ℕ) :
    ∑ j ∈ range (4 * k), f j =
      ∑ i ∈ range k, (f (4 * i) + f (4 * i + 1) + f (4 * i + 2) + f (4 * i + 3)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp [Finset.sum_range_succ]

theorem sum_parity (k : ℕ) (A C : ℤ) :
    ∑ j ∈ range (4 * k), (if j % 2 = 0 then A else C) = 2 * k * A + 2 * k * C := by
  rw [sum_range_four_mul]
  have e : ∀ i ∈ range k, ((if 4 * i % 2 = 0 then A else C) +
      (if (4 * i + 1) % 2 = 0 then A else C) + (if (4 * i + 2) % 2 = 0 then A else C) +
      (if (4 * i + 3) % 2 = 0 then A else C)) = 2 * A + 2 * C := by
    intro i _
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega)]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem sum_sign_parity (k : ℕ) (A C : ℤ) :
    ∑ j ∈ range (4 * k), (-1) ^ j * (if j % 2 = 0 then A else C) = 2 * k * A - 2 * k * C := by
  rw [sum_range_four_mul]
  have e : ∀ i ∈ range k, ((-1) ^ (4 * i) * (if 4 * i % 2 = 0 then A else C) +
      (-1) ^ (4 * i + 1) * (if (4 * i + 1) % 2 = 0 then A else C) +
      (-1) ^ (4 * i + 2) * (if (4 * i + 2) % 2 = 0 then A else C) +
      (-1) ^ (4 * i + 3) * (if (4 * i + 3) % 2 = 0 then A else C) : ℤ) = 2 * A - 2 * C := by
    intro i _
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega), Even.neg_one_pow ⟨2 * i, by ring⟩, Odd.neg_one_pow ⟨2 * i, by ring⟩,
      Even.neg_one_pow ⟨2 * i + 1, by ring⟩, Odd.neg_one_pow ⟨2 * i + 1, by ring⟩]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem sum_four_parity (k : ℕ) (A C : ℤ) :
    ∑ j ∈ range (4 * k), (if j % 4 = 0 then (1 : ℤ) else if j % 4 = 2 then -1 else 0) *
      (if j % 2 = 0 then A else C) = 0 := by
  rw [sum_range_four_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ite_eq_left (show 4 * i % 4 = 0 by omega), ite_eq_left (show 4 * i % 2 = 0 by omega),
    ite_eq_right (show ¬(4 * i + 1) % 4 = 0 by omega),
    ite_eq_right (show ¬(4 * i + 1) % 4 = 2 by omega),
    ite_eq_right (show ¬(4 * i + 2) % 4 = 0 by omega),
    ite_eq_left (show (4 * i + 2) % 4 = 2 by omega),
    ite_eq_left (show (4 * i + 2) % 2 = 0 by omega),
    ite_eq_right (show ¬(4 * i + 3) % 4 = 0 by omega),
    ite_eq_right (show ¬(4 * i + 3) % 4 = 2 by omega)]
  ring

def model (k : ℕ) (x y δ ε : ℤ) (j : ℕ) : ℤ :=
  (if j % 2 = 0 then x - ε else y) + (if j = 0 then ε else 0) + (if j = 2 * k then ε - δ else 0)

variable {k : ℕ} {x y δ ε : ℤ}

theorem sum_model (hk : 1 ≤ k) :
    ∑ j ∈ range (4 * k), model k x y δ ε j = 2 * k * (x - ε) + 2 * k * y + ε + (ε - δ) := by
  simp only [model, Finset.sum_add_distrib, sum_parity, Finset.sum_ite_eq', Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]

theorem sum_sign_model (hk : 1 ≤ k) :
    ∑ j ∈ range (4 * k), (-1) ^ j * model k x y δ ε j =
      2 * k * (x - ε) - 2 * k * y + ε + (ε - δ) := by
  have e : ∀ j, (-1 : ℤ) ^ j * model k x y δ ε j =
      (-1) ^ j * (if j % 2 = 0 then x - ε else y) + (if j = 0 then (-1) ^ j * ε else 0) +
      (if j = 2 * k then (-1) ^ j * (ε - δ) else 0) := by
    intro j
    unfold model
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, sum_sign_parity, Finset.sum_ite_eq', Finset.mem_range]
  rw [ite_eq_left (by omega), ite_eq_left (by omega), pow_zero,
    Even.neg_one_pow ⟨k, by ring⟩]
  ring

theorem orderFourValue_model (hk : 1 ≤ k) (hke : Even k) :
    orderFourValue k (model k x y δ ε) = ε + (ε - δ) := by
  unfold orderFourValue
  have e : ∀ j, (if j % 4 = 0 then model k x y δ ε j
      else if j % 4 = 2 then -model k x y δ ε j else 0) =
      (if j % 4 = 0 then (1 : ℤ) else if j % 4 = 2 then -1 else 0) *
        (if j % 2 = 0 then x - ε else y) +
      (if j = 0 then (if j % 4 = 0 then (1 : ℤ) else if j % 4 = 2 then -1 else 0) * ε else 0) +
      (if j = 2 * k then (if j % 4 = 0 then (1 : ℤ) else if j % 4 = 2 then -1 else 0) * (ε - δ)
        else 0) := by
    intro j
    unfold model
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, sum_four_parity, Finset.sum_ite_eq', Finset.mem_range]
  obtain ⟨m, hm⟩ := hke
  rw [ite_eq_left (show 0 < 4 * k by omega), ite_eq_left (show 2 * k < 4 * k by omega),
    ite_eq_left (show 2 * k % 4 = 0 by omega)]
  simp only [↓reduceIte]
  ring

theorem reflect_even (hk : 1 ≤ k) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * k - 1) :
    (2 * k - 1) * (2 * m) % (4 * k) = 2 * (2 * k - m) := by
  have h : (2 * k - 1) * (2 * m) = 2 * (2 * k - m) + 4 * k * (m - 1) := by
    zify [show 1 ≤ 2 * k by omega, show m ≤ 2 * k by omega, hm1]
    ring
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem odd_eq {Lc : ℕ → ℤ} {o : ℕ → ℕ} {F : ℕ → ℤ}
    (hsymm : ∀ j < 4 * k, Lc ((2 * k - 1) * j % (4 * k)) = Lc j)
    (ho : ∀ j ∈ Finset.Icc 1 (k - 1), Odd (o j) ∧ o j < 4 * k)
    (htrans : ∀ j < 4 * k, Odd j → j = 1 ∨ j = (2 * k - 1) % (4 * k) ∨
      ∃ i ∈ Finset.Icc 1 (k - 1), j = o i ∨ j = (2 * k - 1) * o i % (4 * k))
    (hF : ∀ j ∈ Finset.Icc 1 (k - 1), F j = Lc (o j) - Lc 1)
    (hF0 : ∀ j ∈ Finset.Icc 1 (k - 1), F j = 0) (hk : 1 ≤ k) :
    ∀ j < 4 * k, j % 2 = 1 → Lc j = Lc 1 := by
  intro j hj hodd
  have hoi : ∀ i ∈ Finset.Icc 1 (k - 1), Lc (o i) = Lc 1 := fun i hi => by
    have := hF i hi
    rw [hF0 i hi] at this
    linarith
  rcases htrans j hj (Nat.odd_iff.mpr hodd) with rfl | rfl | ⟨i, hi, rfl | rfl⟩
  · rfl
  · have := hsymm 1 (by omega)
    rwa [mul_one] at this
  · exact hoi i hi
  · rw [hsymm (o i) (ho i hi).2]
    exact hoi i hi

theorem even_eq {Lc : ℕ → ℤ} {E : ℕ → ℤ}
    (hsymm : ∀ j < 4 * k, Lc ((2 * k - 1) * j % (4 * k)) = Lc j)
    (hE : ∀ l ∈ Finset.Icc 1 (k - 1), E l = Lc 0 - Lc (2 * l))
    (hEε : ∀ l ∈ Finset.Icc 1 (k - 1), E l = ε) (hk : 1 ≤ k) :
    ∀ m, 1 ≤ m → m ≤ 2 * k - 1 → m ≠ k → Lc (2 * m) = Lc 0 - ε := by
  have hlow : ∀ l, 1 ≤ l → l ≤ k - 1 → Lc (2 * l) = Lc 0 - ε := fun l h1 h2 => by
    have hl : l ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨h1, h2⟩
    have := hE l hl
    rw [hEε l hl] at this
    linarith
  intro m hm1 hm2 hmk
  by_cases hmk' : m ≤ k - 1
  · exact hlow m hm1 hmk'
  · rw [← hsymm (2 * m) (by omega), reflect_even hk hm1 hm2]
    exact hlow (2 * k - m) (by omega) (by omega)

theorem eq_model {Lc : ℕ → ℤ} {o : ℕ → ℕ} {E F : ℕ → ℤ}
    (hsymm : ∀ j < 4 * k, Lc ((2 * k - 1) * j % (4 * k)) = Lc j)
    (ho : ∀ j ∈ Finset.Icc 1 (k - 1), Odd (o j) ∧ o j < 4 * k)
    (htrans : ∀ j < 4 * k, Odd j → j = 1 ∨ j = (2 * k - 1) % (4 * k) ∨
      ∃ i ∈ Finset.Icc 1 (k - 1), j = o i ∨ j = (2 * k - 1) * o i % (4 * k))
    (hE : ∀ l ∈ Finset.Icc 1 (k - 1), E l = Lc 0 - Lc (2 * l))
    (hF : ∀ j ∈ Finset.Icc 1 (k - 1), F j = Lc (o j) - Lc 1)
    (hF0 : ∀ j ∈ Finset.Icc 1 (k - 1), F j = 0) (hk : 1 ≤ k)
    (hΘδ : Lc 0 - Lc (2 * k) = δ) (hEε : ∀ l ∈ Finset.Icc 1 (k - 1), E l = ε) :
    ∀ j < 4 * k, Lc j = model k (Lc 0) (Lc 1) δ ε j := by
  intro j hj
  unfold model
  by_cases hpar : j % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
    rw [ite_eq_left hpar]
    by_cases hm0 : m = 0
    · subst hm0
      rw [ite_eq_left (by norm_num), ite_eq_right (by omega)]
      ring
    by_cases hmk : m = k
    · subst hmk
      rw [ite_eq_right (by omega), ite_eq_left rfl]
      linarith
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        even_eq hsymm hE hEε hk m (by omega) (by omega) hmk]
      ring
  · rw [ite_eq_right hpar, ite_eq_right (by omega), ite_eq_right (by omega),
      odd_eq hsymm ho htrans hF hF0 hk j hj (by omega)]
    ring

theorem two_dvd_of_eight_dvd {K a W : ℤ} (hK : 0 < K) (h : 8 * K ∣ 4 * K * a + 8 * K * W) :
    2 ∣ a := by
  have h' : 4 * K * 2 ∣ 4 * K * a := by
    have := dvd_sub h (dvd_mul_right (8 * K) W)
    rw [add_sub_cancel_right] at this
    rwa [show 4 * K * 2 = 8 * K by ring]
  exact (mul_dvd_mul_iff_left (by positivity : (4 : ℤ) * K ≠ 0)).mp h'

theorem eight_dvd_of_two_dvd {K a W : ℤ} (h : 2 ∣ a) : 8 * K ∣ 4 * K * a + 8 * K * W := by
  obtain ⟨b, rfl⟩ := h
  exact ⟨b + W, by ring⟩

theorem case_zero {K x y δ P deg : ℤ} (hK : 0 < K) (hδ : δ = 1 ∨ δ = -1)
    (hdeg : deg = 2 * K * (x - δ) + 2 * K * y + δ + (δ - δ))
    (hinv : 2 * K * (x - δ) - 2 * K * y + δ + (δ - δ) = δ + 0 * (1 + P))
    (hS : 8 * K ∣ 4 * K * x + 2 * K * ((δ + 0 * (1 + P)) + (δ + (δ - δ)))) :
    δ * deg ≡ 1 [ZMOD 8 * K] := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hx : 2 ∣ x + δ := two_dvd_of_eight_dvd hK (W := 0) (by convert hS using 1; ring)
  apply Int.modEq_iff_dvd.mpr
  have e : 1 - δ * deg = 4 * K * (1 - δ * x) + 8 * K * 0 := by
    linear_combination (-δ) * hdeg + δ * hinv + (4 * K - 1) * hδ2
  rw [e]
  exact eight_dvd_of_two_dvd (by rcases hδ with rfl | rfl <;> omega)

theorem case_one {K x y δ P t deg : ℤ} (hK : 0 < K) (hKe : Even K) (hδ : δ = 1 ∨ δ = -1)
    (hqe : P - 1 = 2 * K + 4 * K * t)
    (hdeg : deg = 2 * K * (x - δ) + 2 * K * y + δ + (δ - δ))
    (hinv : 2 * K * (x - δ) - 2 * K * y + δ + (δ - δ) = -δ + δ * (1 + P))
    (hS : 8 * K ∣ 4 * K * x + 2 * K * ((-δ + δ * (1 + P)) + (δ + (δ - δ)))) :
    δ * deg ≡ 2 - P [ZMOD 8 * K] := by
  obtain ⟨K', hK'⟩ := hKe
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hx : 2 ∣ x + δ := two_dvd_of_eight_dvd hK (W := K' * δ + K * δ * t) (by
    convert hS using 1
    linear_combination (-2 * K * δ) * hqe - (4 * K * δ) * hK')
  apply Int.modEq_iff_dvd.mpr
  have e : 2 - P - δ * deg = 4 * K * (1 - δ * x) + 8 * K * 0 := by
    linear_combination (-δ) * hdeg + δ * hinv + (4 * K - 2 + P) * hδ2
  rw [e]
  exact eight_dvd_of_two_dvd (by rcases hδ with rfl | rfl <;> omega)

theorem case_two {K x y δ P t deg : ℤ} (hK : 0 < K) (hKe : Even K) (hδ : δ = 1 ∨ δ = -1)
    (hqe : P - 1 = 2 * K + 4 * K * t)
    (hdeg : deg = 2 * K * (x - 0) + 2 * K * y + 0 + (0 - δ))
    (hinv : 2 * K * (x - 0) - 2 * K * y + 0 + (0 - δ) = δ + -δ * (1 + P))
    (hS : 8 * K ∣ 4 * K * x + 2 * K * ((δ + -δ * (1 + P)) + (0 + (0 - δ)))) :
    δ * deg ≡ -P [ZMOD 8 * K] := by
  obtain ⟨K', hK'⟩ := hKe
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hx : 2 ∣ x - δ := two_dvd_of_eight_dvd hK (W := -K' * δ - K * δ * t) (by
    convert hS using 1
    linear_combination (2 * K * δ) * hqe + (4 * K * δ) * hK')
  apply Int.modEq_iff_dvd.mpr
  have e : -P - δ * deg = 4 * K * (-1 - δ * x) + 8 * K * (-t) := by
    linear_combination (-δ) * hdeg + δ * hinv + (-2) * hqe + (2 - P) * hδ2
  rw [e]
  exact eight_dvd_of_two_dvd (by rcases hδ with rfl | rfl <;> omega)

theorem case_three {K x y δ P deg : ℤ} (hK : 0 < K) (hδ : δ = 1 ∨ δ = -1)
    (hdeg : deg = 2 * K * (x - 0) + 2 * K * y + 0 + (0 - δ))
    (hinv : 2 * K * (x - 0) - 2 * K * y + 0 + (0 - δ) = -δ + 0 * (1 + P))
    (hS : 8 * K ∣ 4 * K * x + 2 * K * ((-δ + 0 * (1 + P)) + (0 + (0 - δ)))) :
    δ * deg ≡ 4 * K - 1 [ZMOD 8 * K] := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hx : 2 ∣ x - δ := two_dvd_of_eight_dvd hK (W := 0) (by convert hS using 1; ring)
  apply Int.modEq_iff_dvd.mpr
  have e : 4 * K - 1 - δ * deg = 4 * K * (1 - δ * x) + 8 * K * 0 := by
    linear_combination (-δ) * hdeg + δ * hinv + hδ2
  rw [e]
  exact eight_dvd_of_two_dvd (by rcases hδ with rfl | rfl <;> omega)

end DegreeCongruences

open DegreeCongruences in
theorem type_star_degree_congruences (k : ℕ) (hk : 2 ≤ k) (hkpow : ∃ m : ℕ, k = 2 ^ m)
    (q e : ℤ) (he : e = 1 ∨ e = -1) (hqe : e * q - 1 ≡ 2 * k [ZMOD 4 * k])
    (o : ℕ → ℕ) (deg U V δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (Θ : ℤ) (E F : ℕ → ℤ) (Lc : ℕ → ℤ)
    (hsymm : ∀ j < 4 * k, Lc ((2 * k - 1) * j % (4 * k)) = Lc j)
    (ho : ∀ j ∈ Finset.Icc 1 (k - 1), Odd (o j) ∧ o j < 4 * k)
    (htrans : ∀ j < 4 * k, Odd j → j = 1 ∨ j = (2 * k - 1) % (4 * k) ∨
      ∃ i ∈ Finset.Icc 1 (k - 1), j = o i ∨ j = (2 * k - 1) * o i % (4 * k))
    (hΘ : Θ = Lc 0 - Lc (2 * k))
    (hE : ∀ l ∈ Finset.Icc 1 (k - 1), E l = Lc 0 - Lc (2 * l))
    (hF : ∀ j ∈ Finset.Icc 1 (k - 1), F j = Lc (o j) - Lc 1)
    (hdeg : deg = ∑ j ∈ Finset.range (4 * k), Lc j)
    (hinv : ∑ j ∈ Finset.range (4 * k), (-1) ^ j * Lc j = U + V * (1 + e * q))
    (hS : (8 * k : ℤ) ∣ 4 * k * Lc 0 +
      2 * k * (∑ j ∈ Finset.range (4 * k), (-1) ^ j * Lc j + orderFourValue k Lc))
    (hF0 : ∀ j ∈ Finset.Icc 1 (k - 1), F j = 0) :
    (Θ = δ → (∀ l ∈ Finset.Icc 1 (k - 1), E l = δ) → U = δ → V = 0 →
      δ * deg ≡ 1 [ZMOD 8 * k]) ∧
    (Θ = δ → (∀ l ∈ Finset.Icc 1 (k - 1), E l = δ) → U = -δ → V = δ →
      δ * deg ≡ 2 - e * q [ZMOD 8 * k]) ∧
    (Θ = δ → (∀ l ∈ Finset.Icc 1 (k - 1), E l = 0) → U = δ → V = -δ →
      δ * deg ≡ -(e * q) [ZMOD 8 * k]) ∧
    (Θ = δ → (∀ l ∈ Finset.Icc 1 (k - 1), E l = 0) → U = -δ → V = 0 →
      δ * deg ≡ 4 * k - 1 [ZMOD 8 * k]) := by
  have _ := he
  have hk1 : 1 ≤ k := by omega
  have hke : Even k := by
    obtain ⟨m, rfl⟩ := hkpow
    rcases m with _ | m
    · norm_num at hk
    · exact ⟨2 ^ m, by rw [pow_succ]; ring⟩
  have hK : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
  have hKe : Even (k : ℤ) := by
    obtain ⟨m, hm⟩ := hke
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  obtain ⟨c, hc⟩ := hqe.dvd
  have hqe' : e * q - 1 = 2 * k + 4 * k * (-c) := by linear_combination -hc
  have key : ∀ ε : ℤ, Θ = δ → (∀ l ∈ Finset.Icc 1 (k - 1), E l = ε) →
      deg = 2 * k * (Lc 0 - ε) + 2 * k * Lc 1 + ε + (ε - δ) ∧
      2 * k * (Lc 0 - ε) - 2 * k * Lc 1 + ε + (ε - δ) = U + V * (1 + e * q) ∧
      (8 * k : ℤ) ∣ 4 * k * Lc 0 + 2 * k * ((U + V * (1 + e * q)) + (ε + (ε - δ))) := by
    intro ε hΘδ hEε
    have hm := eq_model hsymm ho htrans hE hF hF0 hk1 (hΘ ▸ hΘδ) hEε
    have hsum : deg = 2 * k * (Lc 0 - ε) + 2 * k * Lc 1 + ε + (ε - δ) := by
      rw [hdeg, Finset.sum_congr rfl fun j hj => hm j (Finset.mem_range.mp hj), sum_model hk1]
    have hsign : ∑ j ∈ Finset.range (4 * k), (-1) ^ j * Lc j =
        2 * k * (Lc 0 - ε) - 2 * k * Lc 1 + ε + (ε - δ) := by
      rw [Finset.sum_congr rfl fun j hj => by rw [hm j (Finset.mem_range.mp hj)],
        sum_sign_model hk1]
    have hfour : orderFourValue k Lc = ε + (ε - δ) := by
      rw [← orderFourValue_model (x := Lc 0) (y := Lc 1) hk1 hke]
      exact Finset.sum_congr rfl fun j hj => by rw [hm j (Finset.mem_range.mp hj)]
    refine ⟨hsum, hsign.symm.trans hinv, ?_⟩
    rw [hinv, hfour] at hS
    exact hS
  refine ⟨fun hΘδ hEδ hU hV => ?_, fun hΘδ hEδ hU hV => ?_, fun hΘδ hE0 hU hV => ?_,
    fun hΘδ hE0 hU hV => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := key δ hΘδ hEδ
    rw [hU, hV] at h2 h3
    exact case_zero hK hδ h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := key δ hΘδ hEδ
    rw [hU, hV] at h2 h3
    exact case_one hK hKe hδ hqe' h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := key 0 hΘδ hE0
    rw [hU, hV] at h2 h3
    have := case_two hK hKe hδ hqe' h1 h2 h3
    exact this
  · obtain ⟨h1, h2, h3⟩ := key 0 hΘδ hE0
    rw [hU, hV] at h2 h3
    exact case_three hK hδ h1 h2 h3

end CFSG.Semidihedral.FieldFactorOne
