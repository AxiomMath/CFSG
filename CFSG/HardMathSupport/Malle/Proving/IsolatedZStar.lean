module

public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.HardMathSupport.Malle.Proving

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_normal_commutators_of_isolated (M : Subgroup G) {u : G} (huM : u ∈ M)
    (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hiso : ∀ g ∈ M, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) → g * u * g⁻¹ = u) :
    ∃ K : Subgroup M, K.Normal ∧ Odd (Nat.card K) ∧
      ∀ g : M, g * (⟨u, huM⟩ : M) * g⁻¹ * (⟨u, huM⟩ : M)⁻¹ ∈ K := by
  let _ : Fintype M := Fintype.ofFinite M
  have ht1 : (⟨u, huM⟩ : M) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  have ht2 : (⟨u, huM⟩ : M) * ⟨u, huM⟩ = 1 := Subtype.ext (by simpa using hu2)
  have hiso' : ∀ g : M, (g * (⟨u, huM⟩ : M) * g⁻¹) * (⟨u, huM⟩ : M) =
      (⟨u, huM⟩ : M) * (g * (⟨u, huM⟩ : M) * g⁻¹) →
      g * (⟨u, huM⟩ : M) * g⁻¹ = (⟨u, huM⟩ : M) := by
    intro g hg
    apply Subtype.ext
    have h1 := congrArg Subtype.val hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact hiso g.1 g.2 h1
  exact CFSG.ZStar.glauberman_zStar M _ ht1 ht2 hiso'

end CFSG.HardMathSupport.Malle.Proving
