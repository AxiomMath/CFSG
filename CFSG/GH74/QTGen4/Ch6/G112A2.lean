module

public import CFSG.Quasithin.Background.G11Stmts

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin

@[expose] def G112ConclA2_le4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → (G112Conclusion B Γ X ∨ G11.G112Concl6U33 Γ) →
    4 ≤ Module.finrank (ZMod 2) V → Module.finrank (ZMod 2) V ≤ 4 →
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁

@[expose] def G112ConclA2_d4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)),
    G111Hyp B Γ v₁ W X X₀ → G112Concl2 Γ →
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁

theorem g112ConclA2_le4_of_d4 (h : G112ConclA2_d4) : G112ConclA2_le4 := by
  intro V _ _ _ B Γ v₁ W X X₀ hhyp hconcl h4 hle t ht hrk hv₁ ha2
  have hd : Module.finrank (ZMod 2) V = 4 := le_antisymm hle h4
  have hc2 : G112Concl2 Γ := by
    rcases hconcl with hc | hc
    · rcases hc with c | c | c | c | c | c | c | c | c | c | c | c | c
      · have := c.1; omega
      · exact c
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
      · have := c.1; omega
    · have := hc.1; omega
  exact h V B Γ v₁ W X X₀ hhyp hc2 t ht hrk hv₁ ha2

end CFSG.GH74.QTGen4
