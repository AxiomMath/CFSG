module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveEEnd

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial

@[expose] def LSixSwapGOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 → ∀ (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ e' : L ≃* LinearFlag.projectiveSL 6 K,
        (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
          X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
          ∀ htX : t ∈ centralizer (modelToG e' X₀ : Set G), LinearTwoSwapKindAt e' t a b X₀ htX) →
        ∀ c : Fin 6, ∃ W₁ : Subgroup G, Nat.card W₁ = 2 ^ 10 ∧ (∀ w ∈ W₁, w * w = 1) ∧
          W₁ ⊓ centralizer ({t} : Set G) = modelToG e' (pointRadical c) ∧
          ∃ htN : t ∈ normalizer (W₁ : Set G),
            modelToG e' (blockSL (K := K) ({c}ᶜ : Finset (Fin 6))) ≤ normalizer (W₁ : Set G) ∧
            LinearTwoSwapTypeAtNOne e' t c W₁ htN) →
      ∀ e : L ≃* LinearFlag.projectiveSL 6 K,
        (∀ (a b : Fin 6) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 6 K)),
          X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
          ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
        ∃ G₁ : Subgroup G, ⁅G₁, G₁⁆ = G₁ ∧
          G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
          (∀ x ∈ G₁, x * (t * x * t⁻¹) ∈ L) ∧ ∀ y ∈ L, ∃ x ∈ G₁, x * (t * x * t⁻¹) = y

theorem lSixSwapNOneInput_of_gOne
    (h : LSixSwapGOneInput) : LSixSwapNOneInput := by
  intro G _ _ L hset K _ _ hK t ht hKt hhyp e hall
  obtain ⟨G₁, hperf, h₁₂, hδ, hsurj⟩ := h G L hset K hK t ht hKt hhyp e hall
  exact false_of_swapRow_of_gOne_linear_two hset (by norm_num) hK e ht hKt hall hperf h₁₂ hδ hsurj

end CFSG.SeitzReduction.LinearPilot
