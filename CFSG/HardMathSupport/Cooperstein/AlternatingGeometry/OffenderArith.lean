module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender


def gx (m : ℕ) : ℕ := 2 ^ m - (m + 1)

theorem two_pow_ge (m : ℕ) : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self

theorem two_pow_gt {m : ℕ} (h : 2 ≤ m) : m + 1 < 2 ^ m := by
  induction m, h using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

theorem gx_add (m : ℕ) : gx m + (m + 1) = 2 ^ m := Nat.sub_add_cancel (two_pow_ge m)

theorem gx_eq_zero_iff (m : ℕ) : gx m = 0 ↔ m ≤ 1 := by
  constructor
  · intro h
    by_contra hm
    have := two_pow_gt (show 2 ≤ m by omega)
    unfold gx at h; omega
  · intro h; interval_cases m <;> simp [gx]

theorem gx_ge_one {m : ℕ} (h : 2 ≤ m) : 1 ≤ gx m := by
  have := two_pow_gt h
  unfold gx; omega

theorem gx_two : gx 2 = 1 := by decide

theorem gx_ge_four {m : ℕ} (h : 3 ≤ m) : 4 ≤ gx m := by
  induction m, h using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    unfold gx at ih ⊢
    have := two_pow_ge k
    rw [pow_succ]
    omega

theorem two_pow_gt_four {m : ℕ} (h : 4 ≤ m) : 2 * m + 2 < 2 ^ m := by
  induction m, h using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [pow_succ]; omega

theorem gx_le_one_imp {m : ℕ} (h : gx m ≤ 1) : m ≤ 2 := by
  by_contra hm
  have := gx_ge_four (show 3 ≤ m by omega)
  omega

theorem arith_pos {ι : Type*} [Fintype ι] (m : ι → ℕ) (u : ℕ) (hu : 1 ≤ u) (hum : ∀ i, u ≤ m i)
    (hr : 0 < Fintype.card ι)
    (h : ∑ i, gx (m i) + u * Fintype.card ι ≤ 1 + 2 * u) :
    ∑ i, 2 ^ m i ≤ 6 ∨ ∑ i, 2 ^ m i = 8 := by
  classical
  rcases Nat.lt_or_ge (Fintype.card ι) 3 with hr3 | hr3
  · interval_cases hc : Fintype.card ι
    ·
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by simpa using hc : (Finset.univ : Finset ι).card = 1)
      rw [ha, Finset.sum_singleton] at h ⊢
      have hua := hum a
      have h1 : gx (m a) + u ≤ 1 + 2 * u := by omega
      have h2 : m a ≤ 3 := by
        by_contra hm
        have := two_pow_gt_four (show 4 ≤ m a by omega)
        have := gx_add (m a)
        omega
      interval_cases hv : m a <;> simp
    ·
      obtain ⟨a, b, hab, hs⟩ :=
        Finset.card_eq_two.1 (by simpa using hc : (Finset.univ : Finset ι).card = 2)
      rw [hs, Finset.sum_pair hab] at h ⊢
      have h1 : gx (m a) + gx (m b) ≤ 1 := by omega
      have ha2 := gx_le_one_imp (show gx (m a) ≤ 1 by omega)
      have hb2 := gx_le_one_imp (show gx (m b) ≤ 1 by omega)
      have hnot : ¬ (m a = 2 ∧ m b = 2) := by
        rintro ⟨h3, h4⟩
        rw [h3, h4, gx_two] at h1
        omega
      left
      interval_cases hva : m a <;> interval_cases hvb : m b <;> simp_all
  ·
    have hg : ∑ i, gx (m i) + u * 3 ≤ 1 + 2 * u := by
      have : u * 3 ≤ u * Fintype.card ι := Nat.mul_le_mul_left _ hr3
      omega
    have hg0 : ∑ i, gx (m i) = 0 := by omega
    have hu1 : u = 1 := by omega
    have hr3' : Fintype.card ι = 3 := by
      have : u * Fintype.card ι ≤ 1 + 2 * u := by omega
      rw [hu1] at this; omega
    have hall : ∀ i, m i = 1 := by
      intro i
      have h0 := (Finset.sum_eq_zero_iff.1 hg0) i (Finset.mem_univ i)
      have := (gx_eq_zero_iff _).1 h0
      have := hum i
      omega
    left
    simp only [hall, pow_one, Finset.sum_const, Finset.card_univ, hr3', smul_eq_mul]
    omega

theorem arith_fixed {ι : Type*} [Fintype ι] (m : ι → ℕ) (h : ∑ i, gx (m i) = 0) :
    ∀ i, m i ≤ 1 := fun i =>
  (gx_eq_zero_iff _).1 ((Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ i))

theorem arith_nofixed {ι : Type*} [Fintype ι] (m : ι → ℕ) (h : ∑ i, gx (m i) ≤ 1) :
    (∀ i, m i ≤ 2) ∧ ∀ i j, m i = 2 → m j = 2 → i = j := by
  classical
  have hle : ∀ i, gx (m i) ≤ 1 := fun i =>
    le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (gx (m j))) (Finset.mem_univ i)) h
  refine ⟨fun i => gx_le_one_imp (hle i), ?_⟩
  intro i j hi hj
  by_contra hij
  have : gx (m i) + gx (m j) ≤ ∑ k, gx (m k) := by
    have := Finset.sum_le_sum_of_subset (f := fun k => gx (m k)) (Finset.subset_univ {i, j})
    rwa [Finset.sum_pair hij] at this
  rw [hi, hj, gx_two] at this
  omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
