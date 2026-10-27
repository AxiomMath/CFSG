module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {G W : Type*} [Group G] [CommGroup W]

theorem exists_derivation_of_crossedHom (ρ : G →* MulAut W) (hρ : Function.Injective ρ)
    (φ : G → W) (hφ : ∀ g h, φ (g * h) = φ g * ρ g (φ h)) :
    ∃ δ : MulAut W → W, (∀ g, δ (ρ g) = φ g) ∧
      ∀ a ∈ ρ.range, ∀ b ∈ ρ.range, δ (a * b) = δ a * a (δ b) := by
  refine ⟨fun a => φ (Function.invFun ρ a), fun g => ?_, ?_⟩
  · simp only [Function.leftInverse_invFun hρ g]
  · rintro _ ⟨g, rfl⟩ _ ⟨k, rfl⟩
    simp only [← map_mul, Function.leftInverse_invFun hρ _]
    exact hφ g k

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
