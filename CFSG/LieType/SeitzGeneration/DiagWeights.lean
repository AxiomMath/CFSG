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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LieType.SeitzGeneration

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def unitAt (ζ : Kˣ) (a : Fin n) : Fin n → Kˣ := fun l => if l = a then ζ else 1

theorem prod_unitAt (ζ : Kˣ) (a : Fin n) : ∏ l, unitAt ζ a l = ζ := by
  simp [unitAt, Finset.prod_ite_eq']

@[expose] def wt (ζ : Kˣ) (hn : 5 ≤ n) (k : Fin 3) : Fin n → Kˣ :=
  unitAt ζ ⟨k.val, by omega⟩ * (unitAt ζ ⟨k.val + 1, by omega⟩)⁻¹

theorem prod_wt (ζ : Kˣ) (hn : 5 ≤ n) (k : Fin 3) : ∏ l, wt ζ hn k l = 1 := by
  simp only [wt, Pi.mul_apply, Pi.inv_apply]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, prod_unitAt, prod_unitAt, mul_inv_cancel]

theorem wt_pow {ζ : Kˣ} {p : ℕ} (hζ : ζ ^ p = 1) (hn : 5 ≤ n) (k : Fin 3) :
    wt ζ hn k ^ p = 1 := by
  funext l
  simp only [wt, Pi.pow_apply, Pi.mul_apply, Pi.inv_apply, Pi.one_apply, unitAt]
  split_ifs <;> simp [inv_pow, hζ]

theorem wt_entries (ζ : Kˣ) (hn : 5 ≤ n) (i j k : ℤ) :
    (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) ⟨0, by omega⟩ = ζ ^ i ∧
    (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) ⟨1, by omega⟩ = ζ ^ (j - i) ∧
    (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) ⟨2, by omega⟩ = ζ ^ (k - j) ∧
    (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) ⟨3, by omega⟩ = ζ ^ (-k) ∧
    (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) ⟨4, by omega⟩ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [wt, unitAt, Fin.ext_iff, zpow_sub, zpow_neg, Pi.pow_apply, Pi.mul_apply, Pi.inv_apply] <;>
    group

theorem scalar_wt {ζ : Kˣ} {p : ℕ} (hζ : orderOf ζ = p) (hn : 5 ≤ n) {i j k : ℤ}
    (h : ∀ l l' : Fin n, (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) l =
      (wt ζ hn 0 ^ i * wt ζ hn 1 ^ j * wt ζ hn 2 ^ k) l') :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ k := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := wt_entries ζ hn i j k
  have h0 : ζ ^ i = 1 := by rw [← e0, h _ ⟨4, by omega⟩, e4]
  have h1 : ζ ^ (j - i) = 1 := by rw [← e1, h _ ⟨4, by omega⟩, e4]
  have h2 : ζ ^ (k - j) = 1 := by rw [← e2, h _ ⟨4, by omega⟩, e4]
  have d0 : (p : ℤ) ∣ i := hζ ▸ orderOf_dvd_iff_zpow_eq_one.2 h0
  have d1 : (p : ℤ) ∣ j - i := hζ ▸ orderOf_dvd_iff_zpow_eq_one.2 h1
  have d2 : (p : ℤ) ∣ k - j := hζ ▸ orderOf_dvd_iff_zpow_eq_one.2 h2
  have d1' : (p : ℤ) ∣ j := by simpa using dvd_add d1 d0
  refine ⟨d0, d1', ?_⟩
  simpa using dvd_add d2 d1'

end CFSG.LieType.SeitzGeneration
