module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2LiftL
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Kr
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2LiftU

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ}

theorem R3bHyp.main [Finite Γ] [Finite W] (h : R3bHyp π θ τW ι D W₀ V τ) :
    (∀ γ, τ γ = γ → γ ∈ θ.range) ∧ ∃ X : Subgroup Γ, X ⊔ X.map τ = ⊤ ∧ ⁅X, X.map τ⁆ = ⊥ ∧
      Nat.card (X ⊓ X.map τ : Subgroup Γ) ∣ 3 ∧ ∃ ψ : SL3 →* X, Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center SL3 ∧ ∀ g, θ g = (ψ g : Γ) * τ (ψ g) := by
  obtain ⟨e, z, hz, he, hK, d, hd, hdτ, hβ, hX, hspan⟩ := h.exists_cands
  obtain ⟨hKc, hKo⟩ := h.ker_central he hK hz hd hdτ hβ hspan
  interval_cases z
  · exact h.concl_U he hK hX hspan hKc hKo
  · exact h.concl_L he hK hX hspan hKc hKo

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
