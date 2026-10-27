module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveQuaBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylLang

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def LFiveFieldSylowSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      ∃ C : Subgroup G, C ≤ S₀ ∧ C ⊓ W₁ = ⊥ ∧ W₁ ⊔ C = S₀ ∧ t ∈ normalizer (C : Set G)

@[expose] def LFiveFieldTildeSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
      ∃ D : Subgroup G, W₁ ⊓ D = ⊥ ∧ W₁ ⊔ D = seitzTilde W₁ Kc ⊔ zpowers t

section Tilde

variable {G : Type} [Group G]

theorem le_seitzTilde_self (W : Subgroup G) (Kc : Subgroup (seitzHat W)) :
    W ≤ seitzTilde W Kc := by
  intro w hw
  rw [mem_seitzTilde_iff]
  refine ⟨le_normalizer hw, ?_⟩
  have h1 : QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨w, le_normalizer hw⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)
  rw [h1]
  exact one_mem _

end Tilde

theorem lFiveFieldSylowSplitInput_of_tilde (h : LFiveFieldTildeSplitInput) :
    LFiveFieldSylowSplitInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨D, hWD, hsup⟩ := h G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield
  obtain ⟨hS₀p, hS₀N, hodd, htS₀, -⟩ := hS₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNtN : seitzTilde W₁ Kc ≤ normalizer (W₁ : Set G) := seitzTilde_le_normalizer W₁ Kc
  have hW₁p : IsPGroup 2 W₁ := IsPGroup.of_card hW₁c
  have hW₁S₀ : W₁ ≤ S₀ :=
    wOne_le_of_not_two_dvd_relIndex hW₁p hNtN hS₀p hS₀N (le_seitzTilde_self W₁ Kc) hodd
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hcard : Nat.card W₁ = Nat.card (W₁ ⊓ centralizer ({t} : Set G) : Subgroup G) ^ 2 := by
    rw [hW₁t, card_modelToG_pointRadical hK e c, hW₁c]
    norm_num
  have hXN : seitzTilde W₁ Kc ⊔ zpowers t ≤ normalizer (W₁ : Set G) :=
    sup_le hNtN (zpowers_le.2 htN)
  have hDN : D ≤ normalizer (W₁ : Set G) := by
    refine le_trans ?_ hXN
    rw [← hsup]
    exact le_sup_right
  have hsup₀ : W₁ ⊔ ((S₀ ⊔ zpowers t) ⊓ D) = S₀ ⊔ zpowers t :=
    sup_inf_eq_of_le_of_sup_eq (hW₁S₀.trans le_sup_left) (sup_le_sup_right hS₀N _) hDN hsup
  have hWD₀ : W₁ ⊓ ((S₀ ⊔ zpowers t) ⊓ D) = ⊥ := by
    rw [eq_bot_iff, ← hWD]
    exact inf_le_inf_left _ inf_le_right
  exact exists_complement_of_complement_sup_zpowers hW₁2 ht2 hW₁S₀ (hS₀N.trans hNtN) htN htS₀
    hcard hWD₀ hsup₀

end CFSG.SeitzReduction.LinearPilot
