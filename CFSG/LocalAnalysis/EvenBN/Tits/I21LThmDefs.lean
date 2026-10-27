module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Thm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y] [Finite Y]
  (ρ : Y →* (V ≃ₗ[ZMod 2] V)) (t : Y)

@[expose] def Thm107P : Prop :=
  (∀ j : Y, j * j = 1 → j ≠ 1 → 2 ≤ rk (ρ j)) ∧
  (∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F = 4 → ∃ j ∈ F, j ≠ 1 ∧ 4 ≤ rk (ρ j)) ∧
  (∀ S : Sylow 2 Y, t ∈ S → ∀ g : Y, g * t * g⁻¹ ∈ S → ∃ s ∈ S, s * t * s⁻¹ = g * t * g⁻¹) ∧
  Nat.card Y ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2 ∧
  (∀ F : Subgroup Y, (∀ f ∈ F, f * f = 1) → Nat.card F ≤ 8)

end Thm

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
