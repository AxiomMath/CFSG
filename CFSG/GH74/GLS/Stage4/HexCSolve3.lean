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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.Stage4.Hex

variable {F : Type*} [Field F]

theorem solve_A4_lin (h2 : (2 : F) ≠ 0) (u : F) (hu : u ≠ 0) (hu2 : u ^ 2 ≠ 1) (e ν : F)
    (a4 A4 : F → F → F) (ha4 : ∀ s t, a4 s t = 3 * e * s * t ^ 2)
    (C1 : ∀ c c' s, A4 (c + c') s =
      A4 c' s + c * (e * c' * s ^ 3) + A4 c s + (c' * s) * (3 * e * c * s ^ 2))
    (C2 : ∀ c s s', A4 c (s + s') = A4 c s + (A4 c s' + a4 s (c * s') +
      (c * s) * (3 * e * c * s' ^ 2 + 6 * e * (s * (c * s')))))
    (C3 : ∀ τ : Fˣ, ∀ c s, A4 ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = (τ : F) * A4 c s)
    (W : ∀ s, ν * (e * 1 * s ^ 3) + a4 (-s) s = A4 (-1) (-s)) :
    ∀ c s, A4 c s = 2 * e * c ^ 2 * s ^ 3 := by
  set B : F → F → F := fun c s => A4 c s - 2 * e * c ^ 2 * s ^ 3 with hB
  have hBc : ∀ c c' s, B (c + c') s = B c' s + B c s := by
    intro c c' s; simp only [hB]; rw [C1]; ring
  have hBs : ∀ c s s', B c (s + s') = B c s + B c s' := by
    intro c s s'; simp only [hB]; rw [C2, ha4]; ring
  have hBτ : ∀ τ : Fˣ, ∀ c s, B ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = (τ : F) * B c s := by
    intro τ c s
    have hτ := τ.ne_zero
    simp only [hB]; rw [C3]; field_simp
  have hB0 : ∀ s, B 0 s = 0 := by
    intro s; have := hBc 0 0 s; simp at this; linear_combination this
  have hBneg : ∀ c s, B (-c) s = - B c s := by
    intro c s; have := hBc (-c) c s; rw [neg_add_cancel, hB0] at this; linear_combination -this
  have hBs0 : ∀ c, B c 0 = 0 := by
    intro c; have := hBs c 0 0; simp at this; linear_combination this
  have hg : ∀ s, B 1 s = (ν - 1) * e * s ^ 3 := by
    intro s
    have h := W s
    have hb : B (-1) (-s) = B 1 s := by
      have h1 := hBs (-1) s (-s)
      rw [add_neg_cancel, hBs0, hBneg 1 s] at h1
      linear_combination (-1 : F) * h1
    have hA : A4 (-1) (-s) = B (-1) (-s) + 2 * e * (-1) ^ 2 * (-s) ^ 3 := by
      simp only [hB]; ring
    rw [ha4, hA, hb] at h
    linear_combination -h
  have hsq : ∀ x s, B (x ^ 2) s = (ν - 1) * e * x ^ 4 * s ^ 3 := by
    intro x s
    by_cases hx : x = 0
    · subst hx; simp [hB0]
    · have h := hBτ (Units.mk0 x hx) 1 (x * s)
      simp only [Units.val_mk0] at h
      rw [show x⁻¹ * (x * s) = s by field_simp, hg, mul_one] at h
      rw [h]; ring
  have hκ : (ν - 1) * e = 0 := by
    obtain ⟨σ, hσ⟩ : ∃ σ : F, σ = (u⁻¹ - u) / 2 := ⟨_, rfl⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : F, ρ = (u + u⁻¹) / 2 := ⟨_, rfl⟩
    have hρσ : ρ ^ 2 = 1 + σ ^ 2 := by
      rw [hρ, hσ]; field_simp; ring
    have hσ0 : σ ≠ 0 := by
      intro h0
      apply hu2
      have h1 : u⁻¹ - u = 0 := (div_eq_zero_iff.1 (hσ ▸ h0)).resolve_right h2
      have h2' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
      linear_combination (-u) * h1 + h2'
    have h1 := hBc 1 (σ ^ 2) 1
    rw [← hρσ, hsq ρ 1, hg 1, hsq σ 1] at h1
    have h2' : (2 : F) * σ ^ 2 ≠ 0 := mul_ne_zero h2 (pow_ne_zero 2 hσ0)
    have h3' : ((ν - 1) * e) * (2 * σ ^ 2) = 0 := by
      have e4 : ρ ^ 4 = (1 + σ ^ 2) ^ 2 := by rw [← hρσ]; ring
      rw [e4] at h1
      linear_combination h1
    exact (mul_eq_zero.1 h3').resolve_right h2'
  have hg0 : ∀ s, B 1 s = 0 := by
    intro s; rw [hg, hκ]; ring
  have hsq0 : ∀ x s, B (x ^ 2) s = 0 := by
    intro x s; rw [hsq, hκ]; ring
  intro c s
  have hc : ((c + 1) / 2) ^ 2 + (-(((c - 1) / 2) ^ 2)) = c := by field_simp; ring
  have key := hBc (((c + 1) / 2) ^ 2) (-(((c - 1) / 2) ^ 2)) s
  rw [hc, hBneg, hsq0, hsq0] at key
  simp only [hB] at key
  linear_combination key

theorem solve_gamma (h2 : (2 : F) ≠ 0) (γ : F → F → F)
    (G1 : ∀ c c' s, γ (c + c') s = γ c' s + γ c s)
    (G2 : ∀ c s s', γ c (s + s') = γ c s + γ c s' + s * (c * s'))
    (G3 : ∀ τ : Fˣ, ∀ c s, γ ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = γ c s) :
    ∀ c s, γ c s = c * s ^ 2 / 2 := by
  set δ : F → F → F := fun c s => γ c s - c * s ^ 2 / 2 with hδ
  have hδc : ∀ c c' s, δ (c + c') s = δ c' s + δ c s := by
    intro c c' s; simp only [hδ]; rw [G1]; ring
  have hδs : ∀ c s s', δ c (s + s') = δ c s + δ c s' := by
    intro c s s'; simp only [hδ]; rw [G2]; field_simp; ring
  have hδτ : ∀ τ : Fˣ, ∀ c s, δ ((τ : F) ^ 2 * c) ((τ : F)⁻¹ * s) = δ c s := by
    intro τ c s
    have hτ := τ.ne_zero
    simp only [hδ]; rw [G3]; field_simp
  have hδ0 : ∀ s, δ 0 s = 0 := by
    intro s; have := hδc 0 0 s; simp at this; linear_combination this
  have hδneg : ∀ c s, δ (-c) s = - δ c s := by
    intro c s; have := hδc (-c) c s; rw [neg_add_cancel, hδ0] at this; linear_combination -this
  have hδs0 : ∀ c, δ c 0 = 0 := by
    intro c; have := hδs c 0 0; simp at this; linear_combination this
  have hsq : ∀ x s, δ (x ^ 2) s = δ 1 (x * s) := by
    intro x s
    by_cases hx : x = 0
    · subst hx; simp [hδ0, hδs0]
    · have h := hδτ (Units.mk0 x hx) 1 (x * s)
      simp only [Units.val_mk0] at h
      rw [show x⁻¹ * (x * s) = s by field_simp, mul_one] at h
      exact h
  have hall : ∀ c s, δ c s = δ 1 s := by
    intro c s
    have hc : ((c + 1) / 2) ^ 2 + (-(((c - 1) / 2) ^ 2)) = c := by field_simp; ring
    have key := hδc (((c + 1) / 2) ^ 2) (-(((c - 1) / 2) ^ 2)) s
    rw [hc, hδneg, hsq, hsq] at key
    have h := hδs 1 (((c - 1) / 2) * s) s
    have e : ((c - 1) / 2) * s + s = ((c + 1) / 2) * s := by field_simp; ring
    rw [e] at h
    linear_combination key + h
  intro c s
  have h0 := hall 0 s
  rw [hδ0] at h0
  have h1 : δ c s = 0 := by rw [hall c s, ← h0]
  simp only [hδ] at h1
  linear_combination h1

end CFSG.GH74.GLS.Stage4.Hex
