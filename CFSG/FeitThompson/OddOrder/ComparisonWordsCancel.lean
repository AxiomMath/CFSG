module

public import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem comparison_words_cancel (p : ℤ) (t r₁ r₃ w₁ w₂ w₃ : G)
    (h : w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃ = w₁ ^ p * r₃ * w₂ ^ p * t ^ 2 * r₁ * w₃ ^ p) :
    (t ^ 2)⁻¹ * (w₂ ^ (-p) * (r₃⁻¹ * w₁ ^ (-(p - 1)) * r₃) * w₂) * t ^ 2
      = (r₁⁻¹)⁻¹ * w₃ ^ (p - 1) * r₁⁻¹ := by
  have e₁ : w₂ ^ (-p) * r₃⁻¹ * w₁ ^ (-p) * (w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃) *
      (w₃⁻¹ * r₁⁻¹ * (t ^ 2)⁻¹) = w₂ ^ (-p) * (r₃⁻¹ * w₁ ^ (-(p - 1)) * r₃) * w₂ := by
    group
  have e₂ : w₂ ^ (-p) * r₃⁻¹ * w₁ ^ (-p) * (w₁ ^ p * r₃ * w₂ ^ p * t ^ 2 * r₁ * w₃ ^ p) *
      (w₃⁻¹ * r₁⁻¹ * (t ^ 2)⁻¹) = t ^ 2 * (r₁ * w₃ ^ (p - 1) * r₁⁻¹) * (t ^ 2)⁻¹ := by
    group
  rw [← e₁, h, e₂]
  group

theorem comparison_words_cancel_of_conj_eq (p : ℤ) (_hp : 2 ≤ p) (t r₁ r₂ r₃ w₁ w₂ w₃ : G)
    (_h₁ : t * r₂⁻¹ * t = w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃)
    (h₂ : w₁ * r₃ * w₂ * t ^ 2 * r₁ * w₃ = w₁ ^ p * r₃ * w₂ ^ p * t ^ 2 * r₁ * w₃ ^ p) :
    (t ^ 2)⁻¹ * (w₂ ^ (-p) * (r₃⁻¹ * w₁ ^ (-(p - 1)) * r₃) * w₂) * t ^ 2
      = (r₁⁻¹)⁻¹ * w₃ ^ (p - 1) * r₁⁻¹ :=
  comparison_words_cancel p t r₁ r₃ w₁ w₂ w₃ h₂

end CFSG.FeitThompson
