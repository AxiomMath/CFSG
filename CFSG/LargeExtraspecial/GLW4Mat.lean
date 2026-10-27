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

public section

namespace CFSG.LargeExtraspecial.GLW4

open Matrix

abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def J : Mat := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

@[expose] def P : Mat := !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]

@[expose] def R : Mat := !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

@[expose] def N : Mat := !![0,0,1,0; 0,0,0,1; 1,0,1,0; 0,1,0,0]

@[expose] def b₁ : Mat := !![0,1,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]

@[expose] def b₁inv : Mat := !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,1,0]

@[expose] def a₂ : Mat := !![1,0,0,1; 0,1,1,0; 0,1,0,0; 1,0,0,0]

@[expose] def a₂inv : Mat := !![0,0,0,1; 0,0,1,0; 0,1,1,0; 1,0,0,1]

@[expose] def b₂ : Mat := !![1,0,1,1; 0,1,1,0; 0,1,0,0; 1,0,1,0]

@[expose] def b₂inv : Mat := !![0,1,1,1; 0,0,1,0; 0,1,1,0; 1,0,0,1]

@[expose] def c₁ : Mat := !![1,0,1,0; 0,1,0,0; 0,0,1,0; 0,1,0,1]

@[expose] def c₂ : Mat := !![1,1,1,0; 0,1,0,0; 0,0,1,0; 0,0,1,1]

theorem J_transpose : Jᵀ = J := by decide
theorem J_mul_J : J * J = 1 := by decide
theorem P_mul_P : P * P = 1 := by decide
theorem dot_J_self (u : Fin 4 → ZMod 2) : u ⬝ᵥ (J *ᵥ u) = 0 := by
  revert u; decide

theorem N_eq_J_add (i j : Fin 4) : N i j = J i j + J 0 i * J 0 j := by
  fin_cases i <;> fin_cases j <;> decide

theorem b₁_mul_b₁inv : b₁ * b₁inv = 1 := by decide
theorem b₁inv_mul_b₁ : b₁inv * b₁ = 1 := by decide
theorem a₂_mul_a₂inv : a₂ * a₂inv = 1 := by decide
theorem a₂inv_mul_a₂ : a₂inv * a₂ = 1 := by decide
theorem b₂_mul_b₂inv : b₂ * b₂inv = 1 := by decide
theorem b₂inv_mul_b₂ : b₂inv * b₂ = 1 := by decide

theorem sp_P : Pᵀ * J * P = J := by decide
theorem sp_b₁inv : b₁invᵀ * J * b₁inv = J := by decide
theorem sp_a₂inv : a₂invᵀ * J * a₂inv = J := by decide
theorem sp_b₂inv : b₂invᵀ * J * b₂inv = J := by decide

theorem c₁_eq : c₁ = P * b₁ * P * b₁inv := by decide
theorem c₂_eq : c₂ = a₂ * b₂ * a₂inv * b₂inv := by decide

theorem c₁_mul_c₁ : c₁ * c₁ = 1 := by decide
theorem c₂_mul_c₂ : c₂ * c₂ = 1 := by decide
theorem c₁_mul_c₂ : c₁ * c₂ = c₂ * c₁ := by decide

@[expose] def H₁ : Mat := !![0,0,1,0; 0,0,1,1; 1,1,0,0; 0,1,0,0]
@[expose] def H₂ : Mat := !![0,0,1,0; 0,0,0,1; 1,0,0,1; 0,1,1,0]
@[expose] def H₃ : Mat := !![0,0,1,0; 0,0,1,1; 1,1,0,1; 0,1,1,0]
@[expose] def G₁ : Mat := !![1,1,1,0; 0,1,0,0; 0,0,1,0; 0,0,1,1]
@[expose] def G₂ : Mat := !![1,0,1,1; 0,1,1,0; 0,0,1,0; 0,0,0,1]
@[expose] def G₃ : Mat := !![1,1,1,1; 0,1,1,0; 0,0,1,0; 0,0,1,1]
@[expose] def kN : Mat := !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,1,0,1]

theorem H₁_transpose : H₁ᵀ = H₁ := by decide
theorem H₂_transpose : H₂ᵀ = H₂ := by decide
theorem H₃_transpose : H₃ᵀ = H₃ := by decide
theorem N_mul_G₁ : N * G₁ = H₁ := by decide
theorem G₁_mul_G₁ : G₁ * G₁ = 1 := by decide
theorem G₂_mul_G₂ : G₂ * G₂ = 1 := by decide
theorem G₃_mul_G₃ : G₃ * G₃ = 1 := by decide
theorem kN_mul_kN : kN * kN = 1 := by decide
theorem G₃_transpose_mul_H₃ : G₃ᵀ * H₃ = N := by decide
theorem cong_kN_H₁ : kNᵀ * H₁ * kN = H₁ := by decide
theorem cong_kN_H₂ : kNᵀ * H₂ * kN = H₃ := by decide

theorem H₁_alt (u : Fin 4 → ZMod 2) : u ⬝ᵥ (H₁ *ᵥ u) = 0 := by revert u; decide
end CFSG.LargeExtraspecial.GLW4
