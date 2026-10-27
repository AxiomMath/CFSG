module

public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.mem_of_centralizes_rootCenter
    {n i e : ℕ} (h : BenderType K n i e)
    (Q : Sylow 2 K) (σ : MulAut K) (hσ : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z) :
    ∀ s ∈ (Q : Subgroup K), σ s ∈ (Q : Subgroup K) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  obtain ⟨z₀, hz₀, hz₀1⟩ := hc.exists_involution
  have hsurj : Function.Surjective σ.toMonoidHom := σ.surjective
  let Q₁ : Sylow 2 K := Sylow.mapSurjective hsurj Q
  have hQ₁ : (Q₁ : Subgroup K) = (Q : Subgroup K).map σ.toMonoidHom :=
    Sylow.coe_mapSurjective hsurj Q
  have hV : rootCenter (Q : Subgroup K) ≠ ⊥ := fun hbot => hz₀1 (by
    rw [hbot] at hz₀
    exact Subgroup.mem_bot.mp hz₀)
  have hVQ₁ : rootCenter (Q : Subgroup K) ≤ (Q₁ : Subgroup K) := by
    intro z hz
    rw [hQ₁]
    exact ⟨z, rootCenter_le _ hz, hσ z hz⟩
  have hQQ₁ : Q₁ = Q := hc.sylow_eq_of_ne_bot hV (rootCenter_le _) hVQ₁
  intro s hs
  have : σ s ∈ (Q₁ : Subgroup K) := by
    rw [hQ₁]
    exact ⟨s, hs, rfl⟩
  rwa [hQQ₁] at this


end CFSG.GH74.Uniqueness.Bender
