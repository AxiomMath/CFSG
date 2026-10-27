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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Wreathed.FourPointTwelveCharacters

theorem pair_val (a : ℤ) : (a * a + (a - 1) * (a - 1) = 1 ∧ (a = 0 ∨ a = 1)) ∨
    5 ≤ a * a + (a - 1) * (a - 1) := by
  rcases le_or_gt a (-1) with h | h
  · right
    nlinarith
  rcases le_or_gt 2 a with h' | h'
  · right
    nlinarith
  left
  interval_cases a <;> norm_num

theorem et_solve {e t P₂ P₃ r : ℤ} (hP₂ : P₂ = 1 ∨ 5 ≤ P₂) (hP₃ : P₃ = 1 ∨ 5 ≤ P₃)
    (hr : 0 ≤ r)
    (hN : 1 + (e - 1) * (e - 1) + (2 - t) * (2 - t) + (-e - 2 + t) * (-e - 2 + t) + P₂ +
      P₃ + e * e + e * e + t * t + r = 8) :
    e = 0 ∧ P₂ = 1 ∧ P₃ = 1 ∧ ((t = 2 ∧ r = 0) ∨ (t = 1 ∧ r = 1)) := by
  have h1 : 1 ≤ P₂ := by omega
  have h2 : 1 ≤ P₃ := by omega
  have s1 := mul_self_nonneg (e - 1)
  have s2 := mul_self_nonneg (2 - t)
  have s3 := mul_self_nonneg (-e - 2 + t)
  have s4 := mul_self_nonneg t
  have s5 := mul_self_nonneg e
  have he : e * e ≤ 2 := by linarith
  have ht : t * t ≤ 5 := by linarith
  have he1 : e ≤ 1 := by
    by_contra hc
    have hc' : 2 ≤ e := by omega
    have : 4 ≤ e * e := by nlinarith
    linarith
  have he2 : -1 ≤ e := by
    by_contra hc
    have hc' : e ≤ -2 := by omega
    have : 4 ≤ e * e := by nlinarith
    linarith
  have ht1 : t ≤ 2 := by
    by_contra hc
    have hc' : 3 ≤ t := by omega
    have : 9 ≤ t * t := by nlinarith
    linarith
  have ht2 : -2 ≤ t := by
    by_contra hc
    have hc' : t ≤ -3 := by omega
    have : 9 ≤ t * t := by nlinarith
    linarith
  clear s1 s2 s3 s4 s5 he ht
  interval_cases e <;> interval_cases t <;> omega

theorem mul_self_eq_mul_sign {x s : ℤ} (hs : s = 1 ∨ s = -1) : x * x = (x * s) * (x * s) := by
  rcases hs with rfl | rfl <;> ring

theorem c1_solve {pβ pκ pl ε δ vβ vκ vl a₂ a₃ k g r : ℤ}
    (hpβ : pβ = 1 ∨ pβ = -1) (hpκ : pκ = 1 ∨ pκ = -1) (hpl : pl = 1 ∨ pl = -1)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (hP : 1 + vβ * pβ + vκ * pκ + vl * pl = 0)
    (hL : -1 - vβ * pβ + vκ * pκ + vl * pl + k * (2 * ε) = 0)
    (hC : 1 - vβ * pβ + vκ * pκ - vl * pl + g * (2 * δ) = 6)
    (hN : 1 + vβ * vβ + vκ * vκ + vl * vl + a₂ * a₂ + (a₂ - 1) * (a₂ - 1) + a₃ * a₃ +
      (a₃ - 1) * (a₃ - 1) + k * k + k * k + g * g + r = 8) (hr : 0 ≤ r) :
    k = 0 ∧ (a₂ = 0 ∨ a₂ = 1) ∧ (a₃ = 0 ∨ a₃ = 1) ∧ vβ = -pβ ∧
      ((g = 2 * δ ∧ vκ = 0 ∧ vl = 0 ∧ r = 0) ∨ (g = δ ∧ vκ = pκ ∧ vl = -pl ∧ r = 1)) := by
  have huβ : vβ * pβ = ε * k - 1 := by linarith
  have huκ : vκ * pκ = 2 - δ * g := by linarith
  have hul : vl * pl = -(ε * k) - 2 + δ * g := by linarith
  rw [mul_self_eq_mul_sign (x := vβ) hpβ, mul_self_eq_mul_sign (x := vκ) hpκ,
    mul_self_eq_mul_sign (x := vl) hpl, mul_self_eq_mul_sign (x := k) hε,
    mul_self_eq_mul_sign (x := g) hδ, mul_comm k ε, mul_comm g δ, huβ, huκ, hul] at hN
  have p₂ := pair_val a₂
  have p₃ := pair_val a₃
  have hN' : 1 + (ε * k - 1) * (ε * k - 1) + (2 - δ * g) * (2 - δ * g) +
      (-(ε * k) - 2 + δ * g) * (-(ε * k) - 2 + δ * g) + (a₂ * a₂ + (a₂ - 1) * (a₂ - 1)) +
      (a₃ * a₃ + (a₃ - 1) * (a₃ - 1)) + ε * k * (ε * k) + ε * k * (ε * k) +
      δ * g * (δ * g) + r = 8 := by linarith
  obtain ⟨he, hp2, hp3, ht⟩ := et_solve (e := ε * k) (t := δ * g)
    (by rcases p₂ with ⟨h, -⟩ | h <;> omega) (by rcases p₃ with ⟨h, -⟩ | h <;> omega) hr hN'
  have hk : k = 0 := by
    rcases hε with rfl | rfl <;> linarith
  have ha₂ : a₂ = 0 ∨ a₂ = 1 := by
    rcases p₂ with ⟨-, h⟩ | h
    · exact h
    · omega
  have ha₃ : a₃ = 0 ∨ a₃ = 1 := by
    rcases p₃ with ⟨-, h⟩ | h
    · exact h
    · omega
  rw [he] at huβ hul
  have hvβ : vβ = -pβ := by
    rcases hpβ with rfl | rfl <;> linarith
  refine ⟨hk, ha₂, ha₃, hvβ, ?_⟩
  rcases ht with ⟨ht, hr0⟩ | ⟨ht, hr1⟩
  · left
    rw [ht] at huκ hul
    refine ⟨?_, ?_, ?_, hr0⟩
    · rcases hδ with rfl | rfl <;> linarith
    · rcases hpκ with rfl | rfl <;> linarith
    · rcases hpl with rfl | rfl <;> linarith
  · right
    rw [ht] at huκ hul
    refine ⟨?_, ?_, ?_, hr1⟩
    · rcases hδ with rfl | rfl <;> linarith
    · rcases hpκ with rfl | rfl <;> linarith
    · rcases hpl with rfl | rfl <;> linarith

theorem Z_solve {pβ pκ pl ε δ q₂ q₃ zβ zκ zl w₂ w₃ hh g r : ℤ}
    (hpβ : pβ = 1 ∨ pβ = -1) (hpκ : pκ = 1 ∨ pκ = -1) (hpl : pl = 1 ∨ pl = -1)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) (hq₂ : q₂ = 1 ∨ q₂ = -1)
    (hq₃ : q₃ = 1 ∨ q₃ = -1)
    (hN : zβ * zβ + zκ * zκ + zl * zl + w₂ * w₂ + w₂ * w₂ + w₃ * w₃ + w₃ * w₃ + hh * hh +
      hh * hh + g * g + r = 3) (hr : 0 ≤ r)
    (hP : zβ * pβ + zκ * pκ + zl * pl = 0)
    (hL₁ : zβ * -pβ + zκ * pκ + zl * pl + hh * (2 * ε) = 0)
    (hL₂ : zβ * -pβ + zκ * pκ + zl * pl + w₂ * q₂ + w₂ * q₂ + w₃ * q₃ + w₃ * q₃ = 0)
    (hC : zβ * -pβ + zκ * pκ + zl * -pl + g * (2 * δ) = 2) :
    zβ = 0 ∧ w₂ = 0 ∧ w₃ = 0 ∧ hh = 0 ∧
      ((zκ = pκ ∧ zl = -pl ∧ g = 0 ∧ r = 1) ∨ (zκ = 0 ∧ zl = 0 ∧ g = δ ∧ r = 2)) := by
  have huβ : zβ * pβ = ε * hh := by linarith
  have hw : w₂ * q₂ + w₃ * q₃ = ε * hh := by linarith
  rw [mul_self_eq_mul_sign (x := zβ) hpβ, mul_self_eq_mul_sign (x := hh) hε, mul_comm hh ε,
    huβ] at hN
  have s1 := mul_self_nonneg w₂
  have s2 := mul_self_nonneg w₃
  have s3 := mul_self_nonneg zκ
  have s4 := mul_self_nonneg zl
  have s5 := mul_self_nonneg g
  have hh0 : ε * hh = 0 := by
    by_contra hne
    have := mul_self_pos.mpr hne
    have hw2 : w₂ * w₂ = 0 := by linarith
    have hw3 : w₃ * w₃ = 0 := by linarith
    rw [mul_self_eq_zero.mp hw2, mul_self_eq_zero.mp hw3] at hw
    exact hne (by linarith)
  have hhh : hh = 0 := by rcases hε with rfl | rfl <;> linarith
  have hzβ : zβ = 0 := by
    rw [hh0] at huβ
    rcases hpβ with rfl | rfl <;> linarith
  rw [hh0] at hw hN
  have hw' : w₂ = 0 ∧ w₃ = 0 := by
    have b2 : w₂ * w₂ ≤ 1 := by linarith
    have b3 : w₃ * w₃ ≤ 1 := by linarith
    have b2' : -1 ≤ w₂ ∧ w₂ ≤ 1 := by constructor <;> nlinarith
    have b3' : -1 ≤ w₃ ∧ w₃ ≤ 1 := by constructor <;> nlinarith
    obtain ⟨b21, b22⟩ := b2'
    obtain ⟨b31, b32⟩ := b3'
    clear s1 s2 b2 b3
    rcases hq₂ with rfl | rfl <;> rcases hq₃ with rfl | rfl <;>
      interval_cases w₂ <;> interval_cases w₃ <;> omega
  obtain ⟨hw2, hw3⟩ := hw'
  rw [hw2, hw3] at hN
  rw [hzβ] at hP hC
  have hul : zl * pl = -(zκ * pκ) := by linarith
  have hug : δ * g = 1 - zκ * pκ := by linarith
  rw [mul_self_eq_mul_sign (x := zκ) hpκ, mul_self_eq_mul_sign (x := zl) hpl,
    mul_self_eq_mul_sign (x := g) hδ, mul_comm g δ, hul, hug] at hN
  have t3 := mul_self_nonneg (zκ * pκ)
  have t4 := mul_self_nonneg (1 - zκ * pκ)
  generalize hz : zκ * pκ = z at hN hul hug t3 t4
  have hzb : -1 ≤ z ∧ z ≤ 1 := by constructor <;> nlinarith
  obtain ⟨hz1, hz2⟩ := hzb
  refine ⟨hzβ, hw2, hw3, hhh, ?_⟩
  clear s1 s2 s3 s4 s5 t3 t4
  interval_cases z
  · omega
  · right
    refine ⟨?_, ?_, ?_, by omega⟩
    · rcases hpκ with rfl | rfl <;> linarith
    · rcases hpl with rfl | rfl <;> linarith
    · rcases hδ with rfl | rfl <;> linarith
  · left
    refine ⟨?_, ?_, ?_, by omega⟩
    · rcases hpκ with rfl | rfl <;> linarith
    · rcases hpl with rfl | rfl <;> linarith
    · rcases hδ with rfl | rfl <;> linarith

theorem sign_mul_pos_eq {q p d d' : ℤ} (hq : q = 1 ∨ q = -1) (hp : p = 1 ∨ p = -1)
    (hd : 1 ≤ d) (hd' : 1 ≤ d') (h : q * d = -(p * d')) : d = d' ∧ q = -p := by
  rcases hq with rfl | rfl <;> rcases hp with rfl | rfl <;> constructor <;> linarith

theorem degree_solve {pβ pκ pl ε δ ζ q₂ q₃ dβ dκ dl d₂ d₃ dη dγ dψ : ℤ}
    (hpκ : pκ = 1 ∨ pκ = -1) (hpl : pl = 1 ∨ pl = -1) (hq₂ : q₂ = 1 ∨ q₂ = -1)
    (hq₃ : q₃ = 1 ∨ q₃ = -1) (hdκ : 1 ≤ dκ) (hdl : 1 ≤ dl) (hd₂ : 1 ≤ d₂) (hd₃ : 1 ≤ d₃)
    (hP : 1 + pβ * dβ + pκ * dκ + pl * dl = 0)
    (hL₁ : -1 - pβ * dβ + pκ * dκ + pl * dl + 2 * ε * dη = 0)
    (hL₂ : -1 - pβ * dβ + pκ * dκ + pl * dl + 2 * (q₂ * d₂) + 2 * (q₃ * d₃) = 0)
    (hC₂ : 1 - pβ * dβ + pκ * dκ - pl * dl + 2 * δ * dγ = 0)
    (hC₁ : 1 - pβ * dβ + 2 * δ * dγ - q₂ * d₂ + q₃ * d₃ = 0)
    (hCs : 1 - pβ * dβ + 2 * δ * dγ + ζ * dψ = 0) :
    ε * dη = 1 + pβ * dβ ∧ δ * dγ = -1 - pκ * dκ ∧ ζ * dψ = 1 + pβ * dβ + 2 * (pκ * dκ) ∧
      d₂ = dκ ∧ q₂ = -pκ ∧ d₃ = dl ∧ q₃ = -pl := by
  have e1 : ε * dη = 1 + pβ * dβ := by linarith
  have e2 : δ * dγ = -1 - pκ * dκ := by linarith
  have e3 : ζ * dψ = 1 + pβ * dβ + 2 * (pκ * dκ) := by linarith
  have e4 : q₂ * d₂ = -(pκ * dκ) := by linarith
  have e5 : q₃ * d₃ = -(pl * dl) := by linarith
  obtain ⟨f1, f2⟩ := sign_mul_pos_eq hq₂ hpκ hd₂ hdκ e4
  obtain ⟨f3, f4⟩ := sign_mul_pos_eq hq₃ hpl hd₃ hdl e5
  exact ⟨e1, e2, e3, f1, f2, f3, f4⟩

end CFSG.Wreathed.FourPointTwelveCharacters
