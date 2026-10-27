module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGrCount

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def LFiveGraphTransferInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
      ∃ H Y : Subgroup G, ¬ 2 ∣ H.index ∧ Y.relIndex H = 2 ∧ t ∈ H ∧ t ∉ Y ∧
        ∀ g : G, g⁻¹ * t * g ∈ Y → g⁻¹ * t * g ∈ seitzTilde W₁ Kc

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldTypeAtNOne_of_transfer
    (hset : SeitzSetting G L)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL 5 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (c : Fin 5) {W₁ : Subgroup G} (hW₁c : Nat.card W₁ = 2 ^ 8) (hW₁2 : ∀ w ∈ W₁, w * w = 1)
    (hW₁t : W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c))
    (htN : t ∈ normalizer (W₁ : Set G))
    (hLN : modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G))
    {Kc : Subgroup (seitzHat W₁)} (hfield : IsFieldTypeComponentAtNOne e t c W₁ htN Kc)
    {H Y : Subgroup G} (hH : ¬ 2 ∣ H.index) (hY : Y.relIndex H = 2) (htH : t ∈ H)
    (htY : t ∉ Y) (hYt : ∀ g : G, g⁻¹ * t * g ∈ Y → g⁻¹ * t * g ∈ seitzTilde W₁ Kc) :
    False := by
  have : IsSimpleGroup G := hset.1
  have hG2 : 2 < Nat.card G := by
    have h1 := Subgroup.card_le_card_group L
    rw [Nat.card_congr e.toEquiv, card_projectiveSL_five_of_card_two hK] at h1
    omega
  have hcount := not_conj_mem_seitzTilde hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  refine CFSG.SeitzReduction.not_exists_normal_index_two_of_simple hG2 ?_
  refine F4Pilot.exists_normal_index_two_of_not_fused_of_relIndex_eq_two hY hH htH htY (a := 1)
    (by rw [pow_one]; exact ht) (fun y _ hyY _ => ?_) (fun g hg => hcount g (hYt g hg))
  have hy1 : y ≠ 1 := fun h => hyY (h ▸ Y.one_mem)
  have hpos := orderOf_pos y
  have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  rw [ht]
  omega

end Transfer

theorem lFiveFieldNOneGraphInput_of_transfer
    (hT : LFiveGraphTransferInput) :
    LFiveFieldNOneGraphInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN hfield
  obtain ⟨Kc, hKc⟩ := (linearTwoFieldTypeAtNOne_iff e t c W₁ htN).1 hfield
  obtain ⟨H, Y, hH, hY, htH, htY, hYt⟩ :=
    hT G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc
  exact false_of_fieldTypeAtNOne_of_transfer hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hKc hH hY
    htH htY hYt

theorem lFiveFieldNOneInput_of_transfer
    (hT : LFiveGraphTransferInput) :
    LFiveFieldNOneInput :=
  lFiveFieldNOneInput_of_graph (lFiveFieldNOneGraphInput_of_transfer hT)

end CFSG.SeitzReduction.LinearPilot
