module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveD

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

@[expose] def LFiveFieldNOneInnerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ g ∈ centralizer ({t} : Set G), ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      LinearTwoFieldTypeAtNOne e t c W₁ htN → False

@[expose] def LFiveFieldNOneGraphInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
      LinearTwoFieldTypeAtNOne e t c W₁ htN → False

theorem lFiveFieldNOneInput_of_inner_of_graph (hI : LFiveFieldNOneInnerInput)
    (hG : LFiveFieldNOneGraphInput) : LFiveFieldNOneInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN hfield
  by_cases hinner : ∀ g ∈ centralizer ({t} : Set G), ∃ l ∈ L, ∀ x ∈ L,
      g * x * g⁻¹ = l * x * l⁻¹
  · exact hI G L hset K hK e t ht hKt hinner c W₁ hW₁c hW₁2 hW₁t htN hLN hfield
  · push Not at hinner
    exact hG G L hset K hK e t ht hKt hinner c W₁ hW₁c hW₁2 hW₁t htN hLN hfield

theorem centralizer_le_sup_zpowers_of_inner {G : Type} [Group G] {L : Subgroup G} {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hinner : ∀ g ∈ centralizer ({t} : Set G), ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹) :
    centralizer ({t} : Set G) ≤ L ⊔ zpowers t := by
  have htC : t ∈ centralizer (L : Set G) := by
    have h := mem_zpowers t
    rw [← hKt] at h
    exact (mem_inf.1 h).1
  intro g hg
  obtain ⟨l, hl, hgl⟩ := hinner g hg
  have hlt : l * t = t * l := (mem_centralizer_iff.1 htC) l hl
  have hmemL : l⁻¹ * g ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hgl x hx
    calc x * (l⁻¹ * g) = l⁻¹ * (l * x * l⁻¹) * g := by group
      _ = l⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = l⁻¹ * g * x := by group
  have hmemt : l⁻¹ * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hgt : g * t = t * g := mem_centralizer_singleton_iff.1 hg
    have hlt' : l⁻¹ * t = t * l⁻¹ := by
      calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt]
        _ = t * l⁻¹ := by group
    calc l⁻¹ * g * t = l⁻¹ * (g * t) := by group
      _ = l⁻¹ * (t * g) := by rw [hgt]
      _ = (l⁻¹ * t) * g := by group
      _ = t * l⁻¹ * g := by rw [hlt']
      _ = t * (l⁻¹ * g) := by group
  have hz : l⁻¹ * g ∈ zpowers t := by
    rw [← hKt]
    exact mem_inf.2 ⟨hmemL, hmemt⟩
  have hgeq : g = l * (l⁻¹ * g) := by group
  rw [hgeq]
  exact mul_mem (mem_sup_left hl) (mem_sup_right hz)

end CFSG.SeitzReduction.LinearPilot
