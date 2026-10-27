module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveTMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

theorem card_centralizer_inv_mul_mul_eq {G : Type} [Group G] (x g : G) :
    Nat.card (centralizer ({g⁻¹ * x * g} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun y => ?_)
  simp only [mem_centralizer_singleton_iff, MulAut.conj_apply, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv]
  constructor
  · intro h
    calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [h]
      _ = x * (g * y * g⁻¹) := by group
  · intro h
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * x * g) * y := by group

@[expose] def LFiveGraphCosetThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧ ∀ s ∈ S₀, s * d₁ * (s * d₁) = 1 →
        27 ∣ Nat.card (centralizer ({s * d₁} : Set G))

theorem lFiveGraphCosetInput_of_three (h3 : LFiveGraphCosetThreeInput) :
    LFiveGraphCosetInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨d₁, hd₁, h27⟩ := h3 G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  refine ⟨d₁, hd₁, fun g s hs hgs => ?_⟩
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hinv : s * d₁ * (s * d₁) = 1 := by
    rw [← hgs]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have hdvd := h27 s hs hinv
  rw [← hgs, card_centralizer_inv_mul_mul_eq] at hdvd
  have hC := card_centralizer_dvd_two_pow_twelve_mul hset hK e ht hKt
  have h1 : 27 ∣ 2 ^ 12 * 9765 := hdvd.trans hC
  exact absurd h1 (by decide)

theorem lFiveGraphTransferInput_of_sylowData_of_three
    (hS : LFiveGraphSylowDataInput)
    (h3 : LFiveGraphCosetThreeInput) : LFiveGraphTransferInput :=
  lFiveGraphTransferInput_of_sylowData_of_coset hS (lFiveGraphCosetInput_of_three h3)

end CFSG.SeitzReduction.LinearPilot
