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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F : Type*} [Field F]

theorem solve_stage1 (h2 : (2 : F) ≠ 0) (a2 A2 Mg ML : F → F → F) (κ : F)
    (H1 : ∀ s t, ML s t = κ * (s * t))
    (H2 : ∀ s s' t, a2 (s + s') t = a2 s' t + s * ML s' t + a2 s t)
    (H3 : ∀ τ : Fˣ, ∀ s t, a2 ((τ : F)⁻¹ * s) ((τ : F) * t) = (τ : F)⁻¹ * a2 s t)
    (H4 : ∀ c s t, c * a2 s t = c * s * ML s t - t * Mg c s)
    (H6 : ∀ c c' s, c * A2 c' s + (c' * s) * Mg c s = c' * A2 c s + (c * s) * Mg c' s)
    (H7 : ∀ c s s', A2 c (s + s') = A2 c s + (A2 c s' + s * Mg c s' + a2 s (c * s')))
    (H8 : ∀ τ : Fˣ, ∀ c s, A2 ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = (τ : F)⁻¹ * A2 c s) :
    ∃ e : F, κ = 6 * e ∧ (∀ s t, a2 s t = 3 * e * s ^ 2 * t) ∧ (∀ c s, A2 c s = e * c * s ^ 3) ∧
      (∀ c s, Mg c s = 3 * e * c * s ^ 2) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, κ = 2 * ν := ⟨κ / 2, by field_simp⟩
  have ha2t : ∀ s t, a2 s t = t * a2 s 1 := by
    intro s t
    have h1 := H4 1 s t
    have h1' := H4 1 s 1
    rw [H1] at h1 h1'
    linear_combination h1 - t * h1'
  have hadd : ∀ s s', a2 (s + s') 1 = a2 s' 1 + s * (2 * ν * s') + a2 s 1 := by
    intro s s'
    have := H2 s s' 1
    rw [H1] at this
    simpa using this
  have hhom : ∀ u : F, u ≠ 0 → a2 u 1 = u ^ 2 * a2 1 1 := by
    intro u hu
    have h := H3 (Units.mk0 u⁻¹ (inv_ne_zero hu)) 1 1
    simp only [Units.val_mk0, inv_inv, mul_one] at h
    rw [ha2t u u⁻¹] at h
    calc a2 u 1 = u * (u⁻¹ * a2 u 1) := by field_simp
      _ = u * (u * a2 1 1) := by rw [h]
      _ = u ^ 2 * a2 1 1 := by ring
  have ha0 : a2 0 1 = 0 := by
    have := hadd 0 0
    simp at this
    linear_combination this
  have hν2 : a2 1 1 = ν := by
    have h1 := hadd 1 1
    have h2' := hhom 2 h2
    have e : (1 : F) + 1 = 2 := by norm_num
    rw [e] at h1
    have : 2 * a2 1 1 = 2 * ν := by linear_combination h1 - h2'
    exact mul_left_cancel₀ h2 this
  have hαform : ∀ s, a2 s 1 = ν * s ^ 2 := by
    intro s
    by_cases hs : s = 0
    · subst hs; simp [ha0]
    · rw [hhom s hs, hν2]; ring
  have ha2 : ∀ s t, a2 s t = t * (ν * s ^ 2) := fun s t => by rw [ha2t, hαform]
  have hMg : ∀ c s, Mg c s = ν * c * s ^ 2 := by
    intro c s
    have h := H4 c s 1
    rw [H1, hαform] at h
    linear_combination h
  have hA2 : ∀ c s, A2 c s = c * A2 1 s := by
    intro c s
    have h := H6 c 1 s
    rw [hMg c s, hMg 1 s] at h
    linear_combination -h
  have hρ_add : ∀ s s', A2 1 (s + s') = A2 1 s + A2 1 s' + ν * (s * s' ^ 2 + s ^ 2 * s') := by
    intro s s'
    have h := H7 1 s s'
    rw [hMg 1 s', ha2 s (1 * s')] at h
    linear_combination h
  have hρ0 : A2 1 0 = 0 := by
    have := hρ_add 0 0
    simp at this
    linear_combination this
  have hρ_hom : ∀ u : F, u ≠ 0 → A2 1 u = u ^ 3 * A2 1 1 := by
    intro u hu
    have h := H8 (Units.mk0 u⁻¹ (inv_ne_zero hu)) 1 1
    simp only [Units.val_mk0, inv_inv, mul_one] at h
    rw [hA2 (u⁻¹ ^ 2) u] at h
    calc A2 1 u = u ^ 2 * (u⁻¹ ^ 2 * A2 1 u) := by field_simp
      _ = u ^ 2 * (u * A2 1 1) := by rw [h]
      _ = u ^ 3 * A2 1 1 := by ring
  have hκ : 2 * ν = 2 * (3 * A2 1 1) := by
    have h1 := hρ_add 1 1
    have h2'' := hρ_hom 2 h2
    have e : (1 : F) + 1 = 2 := by norm_num
    rw [e] at h1
    linear_combination h2'' - h1
  have hν3 : ν = 3 * A2 1 1 := mul_left_cancel₀ h2 hκ
  refine ⟨A2 1 1, by linear_combination 2 * hν3, fun s t => ?_, fun c s => ?_, fun c s => ?_⟩
  · rw [ha2, hν3]; ring
  · rw [hA2]
    by_cases hs : s = 0
    · subst hs; simp [hρ0]
    · rw [hρ_hom s hs]; ring
  · rw [hMg, hν3]

end CFSG.GH74.GLS.Stage4.Hex
