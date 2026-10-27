module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Child
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Close

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage0

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.CPrime
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def CData7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t c : G), Hyp7 G L → StepK t L →
    ShapeC' t L c → ∃ m ∈ L, ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p : Fin 6 → G)
      (v₀ : ℕ), RadicalData .plus L U Q P a ψ p ∧
        (∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) ∧ AutCent L Q ∧
        c * m * (c * m) ∈ centralizer (L : Set G) ∧ (∀ x ∈ U, c * m * x * (c * m)⁻¹ ∈ U) ∧
        v₀ < 64 ∧ qfB .plus v₀ = true ∧
        ∀ v, c * m * ψ v * (c * m)⁻¹ = ψ (toMat 6 6 (reflRows .plus v₀) *ᵥ v)

@[expose] def CData9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t c : G), Hyp9 G L → StepK t L →
    ShapeC' t L c → ∃ m ∈ L, ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p : Fin 6 → G)
      (v₀ : ℕ), RadicalData .minus L U Q P a ψ p ∧
        (∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) ∧ AutCent L Q ∧
        c * m * (c * m) ∈ centralizer (L : Set G) ∧ (∀ x ∈ U, c * m * x * (c * m)⁻¹ ∈ U) ∧
        v₀ < 64 ∧ qfB .minus v₀ = true ∧
        ∀ v, c * m * ψ v * (c * m)⁻¹ = ψ (toMat 6 6 (reflRows .minus v₀) *ᵥ v)

@[expose] def DData7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t c r : G), Hyp7 G L → StepK t L →
    ShapeD' t L c r → ∃ m ∈ L, ∃ (U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p : Fin 6 → G)
      (v₀ : ℕ), RadicalData .plus L U Q P a ψ p ∧
        (∀ V : Subgroup G, V ≤ L → IsPGroup 2 V → U ≤ V → V = U) ∧ AutCent L Q ∧
        (∀ n ∈ L ⊔ zpowers r, n ∈ normalizer (Q : Set G) → n ∈ L) ∧
        c * m * (c * m) ∈ centralizer (L : Set G) ∧ (∀ x ∈ U, c * m * x * (c * m)⁻¹ ∈ U) ∧
        v₀ < 64 ∧ qfB .plus v₀ = true ∧
        ∀ v, c * m * ψ v * (c * m)⁻¹ = ψ (toMat 6 6 (reflRows .plus v₀) *ᵥ v)

theorem endgameC'7_of (h : CData7) : EndgameC'7 := by
  intro G _ _ L t c hH hK hC
  obtain ⟨m, hm, U, Q, P, a, ψ, p, v₀, hR, hUmax, hAc, hsq, hcU, hv₀, hq₀, hcact⟩ :=
    h G L t c hH hK hC
  exact false_of_shapeC' hH.1.simple hH.1.nonab hK (hK.shapeC'_mul_right hC hm hsq) hR hUmax hAc
    hcU hv₀ hq₀ hcact

theorem endgameC'9_of (h : CData9) : EndgameC'9 := by
  intro G _ _ L t c hH hK hC
  obtain ⟨m, hm, U, Q, P, a, ψ, p, v₀, hR, hUmax, hAc, hsq, hcU, hv₀, hq₀, hcact⟩ :=
    h G L t c hH hK hC
  exact false_of_shapeC' hH.1.simple hH.1.nonab hK (hK.shapeC'_mul_right hC hm hsq) hR hUmax hAc
    hcU hv₀ hq₀ hcact

theorem endgameD'7_of (h : DData7) : EndgameD'7 := by
  intro G _ _ L t c r hH hK hD
  obtain ⟨m, hm, U, Q, P, a, ψ, p, v₀, hR, hUmax, hAc, hNQ, hsq, hcU, hv₀, hq₀, hcact⟩ :=
    h G L t c r hH hK hD
  exact false_of_shapeD' hH.1.simple hH.1.nonab hK (hK.shapeD'_mul_right hD hm hsq) hNQ hR hUmax
    hAc hcU hv₀ hq₀ hcact

end CFSG.EvenSmallLie.OmegaEight.Stage0
