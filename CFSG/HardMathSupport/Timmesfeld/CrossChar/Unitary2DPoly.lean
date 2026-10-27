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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_mul_apply_of_eigen (Q₀ T : Module.End K V) (hc : Commute Q₀ T) {ν : K} {w : V}
    (hw : T w = ν • w) (b : K[X]) :
    aeval (Q₀ * T) b w = aeval Q₀ (b.comp (C ν * X)) w := by
  induction b using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, add_comp, hp, hq]
  | monomial k a =>
    have hTk : (T ^ k) w = ν ^ k • w := by
      induction k with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Module.End.mul_apply, hw, map_smul, ih, smul_smul, pow_succ, mul_comm]
    have hmul : (Q₀ * T) ^ k = Q₀ ^ k * T ^ k := hc.mul_pow k
    have hcomp : (monomial k a : K[X]).comp (C ν * X) = monomial k (a * ν ^ k) := by
      rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
    rw [hcomp, aeval_monomial, aeval_monomial, hmul]
    simp only [Module.End.mul_apply, Module.algebraMap_end_apply, hTk, map_smul, smul_smul]
    ring_nf

theorem dvd_of_aeval_apply_eq_zero (Q : Module.End K V) {f : K[X]} (hf : Irreducible f)
    (hf0 : aeval Q f = 0) {w : V} (hw : w ≠ 0) {u : K[X]} (hu : aeval Q u w = 0) : f ∣ u := by
  by_contra hnd
  obtain ⟨s, t, hst⟩ := (Irreducible.coprime_iff_not_dvd hf).mpr hnd
  have h1 := congrArg (fun r : K[X] => aeval Q r w) hst
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, hf0, hu,
    map_zero, Module.End.one_apply] at h1
  exact hw (by simpa using h1.symm)

theorem aeval_eq_const (Q₀ T : Module.End K V) (hc : Commute Q₀ T) {f : K[X]}
    (hf : Irreducible f) (hfm : f.Monic) (hdeg : f.natDegree = 3) (h0 : aeval Q₀ f = 0)
    (h1 : aeval (Q₀ * T) f = 0) {ν₁ ν₂ : K} (hν : ν₁ ≠ ν₂) (hν2 : ν₁ ^ 2 ≠ ν₂ ^ 2) {w₁ w₂ : V}
    (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) (e₁ : T w₁ = ν₁ • w₁) (e₂ : T w₂ = ν₂ • w₂) (a b : K[X])
    (hab : aeval Q₀ a = aeval (Q₀ * T) b) :
    ∃ b₀ : K, aeval (Q₀ * T) b = algebraMap K (Module.End K V) b₀ := by
  obtain ⟨b', hb'⟩ : ∃ b' : K[X], b' = b %ₘ f := ⟨_, rfl⟩
  have hb'deg : b'.natDegree < 3 := by
    have := natDegree_modByMonic_lt b hfm (by
      intro h; rw [h] at hdeg; simp at hdeg)
    rw [hb']
    omega
  have hbb : aeval (Q₀ * T) b = aeval (Q₀ * T) b' := by
    have := modByMonic_add_div b f
    conv_lhs => rw [← this]
    rw [map_add, map_mul, h1, zero_mul, add_zero, hb']
  have hcomp : ∀ ν : K, ∀ w : V, T w = ν • w → w ≠ 0 →
      f ∣ a - b'.comp (C ν * X) := by
    intro ν w hw hw0
    refine dvd_of_aeval_apply_eq_zero Q₀ hf h0 hw0 ?_
    rw [map_sub, LinearMap.sub_apply, ← aeval_mul_apply_of_eigen Q₀ T hc hw, ← hbb, ← hab, sub_self]
  have hd1 := hcomp ν₁ w₁ e₁ hw₁
  have hd2 := hcomp ν₂ w₂ e₂ hw₂
  have hD : f ∣ b'.comp (C ν₂ * X) - b'.comp (C ν₁ * X) := by
    have := dvd_sub hd1 hd2
    simpa [sub_sub_sub_cancel_left] using this
  have hdegc : ∀ ν : K, (b'.comp (C ν * X)).natDegree < 3 := by
    intro ν
    refine lt_of_le_of_lt ?_ hb'deg
    calc (b'.comp (C ν * X)).natDegree ≤ b'.natDegree * (C ν * X).natDegree :=
          natDegree_comp_le
      _ ≤ b'.natDegree * 1 := Nat.mul_le_mul_left _ ((natDegree_C_mul_le ν X).trans natDegree_X_le)
      _ = b'.natDegree := mul_one _
  have hD0 : b'.comp (C ν₂ * X) - b'.comp (C ν₁ * X) = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt hD ?_
    rw [hdeg]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt (hdegc ν₂) (hdegc ν₁))
  have hcoef : ∀ k : ℕ, b'.coeff k * (ν₂ ^ k - ν₁ ^ k) = 0 := by
    intro k
    have := congrArg (fun r : K[X] => r.coeff k) hD0
    simp only [coeff_sub, comp_C_mul_X_coeff, coeff_zero] at this
    linear_combination this
  have h1c : b'.coeff 1 = 0 := by
    have := hcoef 1
    simp only [pow_one] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hν
  have h2c : b'.coeff 2 = 0 := by
    have := hcoef 2
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hν2
  have hbC : b' = C (b'.coeff 0) := by
    ext k
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · simp
      · simpa using h1c
      · simpa using h2c
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_C]
      simp only [show k ≠ 0 by omega, ↓reduceIte]
  refine ⟨b'.coeff 0, ?_⟩
  rw [hbb, hbC, aeval_C]
  simp

end CFSG.HardMathSupport.Timmesfeld.CrossChar
