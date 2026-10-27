module

public import CFSG.GroupTheory.OppositeRadicals
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.GroupTheory

theorem hasGoodOppositePRadicals_of_lift {H : Type*} [Group H] [Finite H] {G : Type*} [Group G]
    [Finite G] (ψ : H →* G) (p : ℕ) [Fact p.Prime] (hker : ψ.ker ≤ Subgroup.center H)
    (hinv : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1)
    (hH : ∀ Q : Subgroup H, Q ≠ ⊥ → IsRadicalPGroup p ⊤ Q → HasGoodOppositePRadicals p ⊤ Q)
    {Q : Subgroup G} (hQne : Q ≠ ⊥) (hQ : IsRadicalPGroup p ψ.range Q) :
    HasGoodOppositePRadicals p ψ.range Q := by
  have hrad {X : Subgroup H} :
      IsRadicalPGroup p ⊤ X ↔ pCoreOf p (Subgroup.normalizer (X : Set H)) = X := by
    rw [IsRadicalPGroup, top_inf_eq]
  obtain ⟨V₀, h₁, h₂, h₃, h₄, h₅⟩ := CFSG.StandardType.GGOppRad.exists_opposite_of_lift ψ p hker
    hinv (fun X hXne hX => by
      obtain ⟨V₀, ⟨hV₀, hc, hb⟩, hgen, hconj⟩ := hH X hXne (hrad.mpr hX)
      rw [top_inf_eq] at hb
      exact ⟨V₀, hrad.mp hV₀, hc, hb, hgen, fun V hV hVc hVb =>
        hconj V ⟨hrad.mpr hV, hVc, by rwa [top_inf_eq]⟩⟩) hQne hQ
  exact ⟨V₀, ⟨h₁, h₂, h₃⟩, h₄, fun V ⟨a, b, c⟩ => h₅ V a b c⟩

end CFSG.LieType.SeitzGeneration
