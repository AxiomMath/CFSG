module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup

theorem pow_four_commute_of_commute_conj {G : Type*} [Group G] {P : Subgroup G} {b : G}
    (hP4 : ∀ x ∈ P, x ^ 4 = 1) (hb : b ∈ normalizer (P : Set G))
    (hcomm : ∀ x ∈ P, b * (x⁻¹ * b * x) = (x⁻¹ * b * x) * b) :
    ∀ x ∈ P, b ^ 4 * x = x * b ^ 4 := by
  intro x hx
  have hbP : b⁻¹ * x * b ∈ P := (mem_normalizer_iff''.mp hb x).mp hx
  have hcb : b * (x⁻¹ * b * x) = (x⁻¹ * b * x) * b := hcomm x hx
  have hyP : x⁻¹ * (b⁻¹ * x * b) ∈ P := mul_mem (inv_mem hx) hbP
  set y := x⁻¹ * (b⁻¹ * x * b) with hy
  have hy_eq : y = (x⁻¹ * b * x)⁻¹ * b := by rw [hy]; group
  have hyb : b * y = y * b := by
    rw [hy_eq]
    have h1 : b * (x⁻¹ * b * x)⁻¹ = (x⁻¹ * b * x)⁻¹ * b := by
      calc b * (x⁻¹ * b * x)⁻¹ = (x⁻¹ * b * x)⁻¹ * ((x⁻¹ * b * x) * b) * (x⁻¹ * b * x)⁻¹ := by
            group
        _ = (x⁻¹ * b * x)⁻¹ * (b * (x⁻¹ * b * x)) * (x⁻¹ * b * x)⁻¹ := by rw [hcb]
        _ = (x⁻¹ * b * x)⁻¹ * b := by group
    calc b * ((x⁻¹ * b * x)⁻¹ * b) = (b * (x⁻¹ * b * x)⁻¹) * b := by group
      _ = (x⁻¹ * b * x)⁻¹ * b * b := by rw [h1]
  have hφy : b⁻¹ * y * b = y := by
    calc b⁻¹ * y * b = b⁻¹ * (y * b) := by group
      _ = b⁻¹ * (b * y) := by rw [hyb]
      _ = y := by group
  have hφx : b⁻¹ * x * b = x * y := by rw [hy]; group
  have hφ : ∀ w : G, b⁻¹ * (w * y) * b = (b⁻¹ * w * b) * y := fun w => by
    calc b⁻¹ * (w * y) * b = (b⁻¹ * w * b) * (b⁻¹ * y * b) := by group
      _ = (b⁻¹ * w * b) * y := by rw [hφy]
  have e2 : b⁻¹ * (b⁻¹ * x * b) * b = x * y * y := by rw [hφx, hφ x, hφx]
  have e3 : b⁻¹ * (b⁻¹ * (b⁻¹ * x * b) * b) * b = x * y * y * y := by
    rw [e2, hφ (x * y), hφ x, hφx]
  have e4 : b⁻¹ * (b⁻¹ * (b⁻¹ * (b⁻¹ * x * b) * b) * b) * b = x * y * y * y * y := by
    rw [e3, hφ (x * y * y), hφ (x * y), hφ x, hφx]
  have hy4 : y * y * y * y = 1 := by
    have := hP4 y hyP
    simpa [pow_succ, mul_assoc] using this
  have E : b⁻¹ * (b⁻¹ * (b⁻¹ * (b⁻¹ * x * b) * b) * b) * b = x := by
    rw [e4]
    calc x * y * y * y * y = x * (y * y * y * y) := by group
      _ = x := by rw [hy4, mul_one]
  have hb4 : b ^ 4 = b * b * b * b := by simp [pow_succ, mul_assoc]
  calc b ^ 4 * x = b ^ 4 * (b⁻¹ * (b⁻¹ * (b⁻¹ * (b⁻¹ * x * b) * b) * b) * b) := by rw [E]
    _ = x * b ^ 4 := by rw [hb4]; group

end CFSG.GF2Type.Aschbacher1976HigherCenter
