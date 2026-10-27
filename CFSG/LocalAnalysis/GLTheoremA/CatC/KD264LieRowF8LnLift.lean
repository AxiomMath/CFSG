module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

variable {G P : Type*} [Group G] [Group P]

theorem exists_fixed_lift_of_three (π : G →* P) (hπ : Function.Surjective π)
    (hZc : ∀ g, π g = 1 → ∀ h : G, g * h = h * g) (hZ7 : ∀ g, π g = 1 → g ^ 7 = 1)
    (β : G →* G) (b : P ≃* P) (hb : ∀ g, π (β g) = b (π g)) {x : P} (hx : b x = x)
    (hx3 : x ^ 3 = 1) : ∃ x₂ : G, π x₂ = x ∧ β x₂ = x₂ := by
  obtain ⟨x₁, rfl⟩ := hπ x
  have h13 : π (x₁ ^ 3) = 1 := by rw [map_pow]; exact hx3
  have h21 : x₁ ^ 21 = 1 := by
    have := hZ7 _ h13
    rw [← pow_mul] at this
    exact this
  set x₂ : G := x₁ ^ 7 with hx₂
  have hπx₂ : π x₂ = π x₁ := by
    rw [hx₂, map_pow]
    have : π x₁ ^ 7 = (π x₁ ^ 3) ^ 2 * π x₁ := by group
    rw [this, hx3, one_pow, one_mul]
  have hx₂3 : x₂ ^ 3 = 1 := by
    rw [hx₂, ← pow_mul]
    exact h21
  set z : G := x₂⁻¹ * β x₂ with hz
  have hπz : π z = 1 := by
    rw [hz, map_mul, map_inv, hb, hπx₂, hx, inv_mul_cancel]
  have hzc : ∀ h : G, z * h = h * z := hZc z hπz
  have hz7 : z ^ 7 = 1 := hZ7 z hπz
  have hβx : β x₂ = x₂ * z := by rw [hz]; group
  have hz3 : z ^ 3 = 1 := by
    have h1 : (β x₂) ^ 3 = 1 := by rw [← map_pow, hx₂3, map_one]
    have hcomm : Commute x₂ z := (hzc x₂).symm
    rw [hβx, hcomm.mul_pow, hx₂3, one_mul] at h1
    exact h1
  have hz1 : z = 1 := by
    have := pow_gcd_eq_one.2 ⟨hz7, hz3⟩
    simpa using this
  refine ⟨x₂, hπx₂, ?_⟩
  rw [hβx, hz1, mul_one]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Ln

end
