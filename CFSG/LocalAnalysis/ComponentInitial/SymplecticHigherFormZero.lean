module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem mul_apply_eq_of_zero_iff {b c : M →ₗ[K] N →ₗ[K] K} (h : ∀ v w, b v w = 0 ↔ c v w = 0)
    (v : M) (x w : N) : b v w * c v x = b v x * c v w := by
  have hz := (h v (b v w • x - b v x • w)).1 (by
    simp only [map_sub, map_smul, smul_eq_mul]
    ring)
  simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hz
  exact hz

theorem mul_apply_eq_of_zero_iff' {b c : M →ₗ[K] N →ₗ[K] K} (h : ∀ v w, b v w = 0 ↔ c v w = 0)
    (u v : M) (w : N) : b v w * c u w = b u w * c v w := by
  have hz := (h (b v w • u - b u w • v) w).1 (by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    sub_eq_zero] at hz
  exact hz

theorem form_zero_relation {b c : M →ₗ[K] N →ₗ[K] K} (h : ∀ v w, b v w = 0 ↔ c v w = 0) :
    ∃ μ : Kˣ, ∀ v w, c v w = μ * b v w := by
  by_cases hb : ∀ v w, b v w = 0
  · exact ⟨1, fun v w => by rw [(h v w).1 (hb v w), hb v w, mul_zero]⟩
  push Not at hb
  obtain ⟨v₀, w₀, h₀⟩ := hb
  have hc₀ : c v₀ w₀ ≠ 0 := fun h' => h₀ ((h v₀ w₀).2 h')
  have row := mul_apply_eq_of_zero_iff h
  have col := mul_apply_eq_of_zero_iff' h
  have hrow : ∀ v w, b v w₀ ≠ 0 → b v₀ w₀ * c v w = c v₀ w₀ * b v w := by
    intro v w hv
    apply mul_left_cancel₀ hv
    calc b v w₀ * (b v₀ w₀ * c v w) = b v₀ w₀ * (b v w₀ * c v w) := by ring
      _ = b v₀ w₀ * (b v w * c v w₀) := by rw [row v w w₀]
      _ = b v w * (b v₀ w₀ * c v w₀) := by ring
      _ = b v w * (b v w₀ * c v₀ w₀) := by rw [col v v₀ w₀]
      _ = b v w₀ * (c v₀ w₀ * b v w) := by ring
  have key : ∀ v w, b v₀ w₀ * c v w = c v₀ w₀ * b v w := by
    intro v w
    by_cases hv : b v w₀ = 0
    · by_cases hw : b v₀ w = 0
      · have hs := hrow (v + v₀) w (by rw [map_add, LinearMap.add_apply, hv, zero_add]; exact h₀)
        rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, (h v₀ w).1 hw, hw,
          add_zero, add_zero] at hs
        exact hs
      · apply mul_left_cancel₀ hw
        calc b v₀ w * (b v₀ w₀ * c v w) = b v₀ w₀ * (b v₀ w * c v w) := by ring
          _ = b v₀ w₀ * (b v w * c v₀ w) := by rw [col v v₀ w]
          _ = b v w * (b v₀ w₀ * c v₀ w) := by ring
          _ = b v w * (b v₀ w * c v₀ w₀) := by rw [row v₀ w w₀]
          _ = b v₀ w * (c v₀ w₀ * b v w) := by ring
    · exact hrow v w hv
  refine ⟨Units.mk0 (c v₀ w₀ / b v₀ w₀) (div_ne_zero hc₀ h₀), fun v w => ?_⟩
  rw [Units.val_mk0, div_mul_eq_mul_div, eq_div_iff h₀, mul_comm, key v w]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
