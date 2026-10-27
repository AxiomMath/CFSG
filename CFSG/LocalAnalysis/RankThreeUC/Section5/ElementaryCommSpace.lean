module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryCommSpace

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizer_commutator {H₁ H₂ : Subgroup G} {g : G}
    (h1 : g ∈ Subgroup.normalizer (H₁ : Set G)) (h2 : g ∈ Subgroup.normalizer (H₂ : Set G)) :
    g ∈ Subgroup.normalizer (⁅H₁, H₂⁆ : Subgroup G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (H₁ : Set G) →
      g ∈ Subgroup.normalizer (H₂ : Set G) → ∀ x ∈ (⁅H₁, H₂⁆ : Subgroup G),
      g * x * g⁻¹ ∈ (⁅H₁, H₂⁆ : Subgroup G) := by
    intro g h1 h2 x hx
    have hmap : (⁅H₁, H₂⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ ⁅H₁, H₂⁆ := by
      rw [Subgroup.map_commutator]
      apply Subgroup.commutator_mono
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 h1 y).1 hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 h2 y).1 hy
    exact hmap ⟨x, hx, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g h1 h2 x, fun hx => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer _).inv_mem h1) ((Subgroup.normalizer _).inv_mem h2) _ hx
  simpa [mul_assoc] using this

theorem commutator_le_left {H₁ H₂ : Subgroup G} (h : H₂ ≤ Subgroup.normalizer (H₁ : Set G)) :
    ⁅H₁, H₂⁆ ≤ H₁ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ H₁ := by
    have := (Subgroup.mem_normalizer_iff.1 (h hy) x⁻¹).1 (H₁.inv_mem hx)
    simpa [mul_assoc] using this
  have := H₁.mul_mem hx h1
  simpa [commutatorElement_def, mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeUC.Section5.ElementaryCommSpace
