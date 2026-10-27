module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSPart
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

@[expose] def LFiveSOneSylowPartInput : Prop :=
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
      ∃ (a b d d' : Fin 5) (_ : a ≠ b) (hdd' : d ≠ d'), c ≠ a ∧ c ≠ b ∧
        ({c}ᶜ : Finset (Fin 5)) \ {a, b} = {d, d'} ∧
        ∃ X₀ : Subgroup (LinearFlag.projectiveSL 5 K), X₀ ≤ rootSL2 a b ∧
          Nat.card X₀ = Nat.card K + 1 ∧
        ∃ C S₀ : Subgroup G, Nat.card C = 2 ^ 6 ∧ IsPGroup 2 C ∧
          C ≤ normalizer (W₁ : Set G) ∧ C ≤ centralizer ({t} : Set G) ∧
          C ⊓ centralizer ((W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) = ⊥ ∧
          W₁ ≤ S₀ ∧ S₀ ≤ W₁ ⊔ C ∧
          S₀ ≤ centralizer ((W₁ ⊓ centralizer (modelToG e X₀ : Set G) : Subgroup G) : Set G) ∧
          C ≤ S₀ ⊔ zpowers ((e.symm (xab hdd' 1) : L) : G) ∧
          2 ^ 15 ≤ 4 * Nat.card S₀ ∧
          ∀ h ∈ C, h * h = 1 → Nat.card (W₁ ⊓ centralizer ({h * t} : Set G) : Subgroup G) ≤
            Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G)

theorem lFiveSOneSwapDataInput_of_sylowPart
    (h : LFiveSOneSylowPartInput) : LFiveSOneSwapDataInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hall hcore c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  obtain ⟨a, b, d, d', hab, hdd', hca, hcb, hS, X₀, hX₀, hX₀c, C, S₀, hCc, hC2, hCW, hCt, hCV,
    hWS₀, hS₀, hS₀C, hCgen, hS₀c, hkey⟩ :=
    h G L hset K hK e t ht hKt hall hcore c W₁ hW₁c hW₁2 hW₁t htW₁ hLW
  obtain ⟨A, X, hinf, hcomm, htW₀, hE1, huA, huW₀, hX2, hXA, hXW₀, hXE, hk, -, -⟩ :=
    swapPart_five_of_swap hset hK e ht hKt c hW₁c hW₁2 hW₁t htW₁ hLW hab hdd' hca hcb hS hX₀ hX₀c
      (hall a b hab X₀ hX₀ hX₀c)
  refine ⟨C, S₀, zpowers ((e.symm (xab hdd' 1) : L) : G),
    W₁ ⊓ centralizer (modelToG e X₀ : Set G), A, X, 4, hCc, hC2, hCW, hCt, hCV, hWS₀, hS₀, hS₀C,
    hCgen, ?_, hinf, hcomm, htW₀, hE1, huA, huW₀, hX2, hXA, hXW₀, hXE, hk, hkey⟩
  rw [hW₁c, hCc]
  norm_num
  omega

theorem lFiveSOneNotSylowCoreInput_of_sylowPart
    (h : LFiveSOneSylowPartInput) : LFiveSOneNotSylowCoreInput :=
  lFiveSOneNotSylowCoreInput_of_swapData (lFiveSOneSwapDataInput_of_sylowPart h)

end CFSG.SeitzReduction.LinearPilot
