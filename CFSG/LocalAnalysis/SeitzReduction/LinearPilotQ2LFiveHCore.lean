module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHInput
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveHRoot

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

@[expose] def LFiveSOneNotSylowCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        ∀ htX : t ∈ centralizer (modelToG e X₀ : Set G), LinearTwoSwapKindAt e t a b X₀ htX) →
      (∀ (a b : Fin 5) (_ : a ≠ b) (X₀ : Subgroup (LinearFlag.projectiveSL 5 K)),
        X₀ ≤ rootSL2 a b → Nat.card X₀ = Nat.card K + 1 →
        modelToG e (rootSL2 (K := K) a b) ≤
          centralizer (centralizerPerfectCore (modelToG e X₀) : Set G)) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
      t ∈ normalizer (W₁ : Set G) →
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ normalizer (W₁ : Set G) ∧ 2 ^ 15 < Nat.card P

theorem lFiveSOneNotSylowSwapInput_of_core
    (h : LFiveSOneNotSylowCoreInput) : LFiveSOneNotSylowSwapInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  have htC : t ∈ centralizer (L : Set G) := mem_centralizer_of_inf_eq_zpowers hKt
  refine h G L hset K hK e t ht hKt hall (fun a b hab X₀ hX₀ hX₀c => ?_) c W₁ hW₁c hW₁2 hW₁t
    htW₁ hLW
  have htX : t ∈ centralizer (modelToG e X₀ : Set G) := centralizer_le (modelToG_le e X₀) htC
  exact rootSL2_le_centralizer_of_swap_five hset hK e htC ht hab hX₀ hX₀c htX
    (hall a b hab X₀ hX₀ hX₀c htX)

end CFSG.SeitzReduction.LinearPilot
