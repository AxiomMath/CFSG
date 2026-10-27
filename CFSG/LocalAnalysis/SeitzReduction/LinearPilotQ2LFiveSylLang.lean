module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylMain
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def LFiveThompsonFieldQuotInput : Prop :=
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
    ∀ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      ∀ u ∈ S₀, u * t * (u * t) ∈ W₁ → ∃ v ∈ S₀, v⁻¹ * (u * t) * v * t⁻¹ ∈ W₁

section TypeFree

variable {G : Type} [Group G] [Finite G]

theorem wOne_le_of_not_two_dvd_relIndex {W N S₀ : Subgroup G} (hW : IsPGroup 2 W)
    (hNW : N ≤ normalizer (W : Set G)) (hS₀p : IsPGroup 2 S₀) (hS₀N : S₀ ≤ N)
    (hW₀ : W ≤ N) (hodd : ¬ 2 ∣ S₀.relIndex N) : W ≤ S₀ := by
  have hP : IsPGroup 2 (S₀ ⊔ W : Subgroup G) := hS₀p.to_sup_of_normal_right' hW (hS₀N.trans hNW)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hdvd : Nat.card (S₀ ⊔ W : Subgroup G) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le (sup_le hS₀N hW₀)
  have hNc : Nat.card N = S₀.relIndex N * Nat.card S₀ := by
    have h := Subgroup.relIndex_mul_card (H := S₀) (K := N)
    rw [inf_of_le_left hS₀N] at h
    exact h.symm
  rw [hNc, hk] at hdvd
  have hr : Nat.Coprime (2 ^ k) (S₀.relIndex N) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have h2 : 2 ^ k ∣ Nat.card S₀ := hr.dvd_of_dvd_mul_left hdvd
  have hle : Nat.card (S₀ ⊔ W : Subgroup G) ≤ Nat.card S₀ := by
    rw [hk]
    exact Nat.le_of_dvd Nat.card_pos h2
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : S₀ ≤ S₀ ⊔ W) hle
  rw [heq]
  exact le_sup_right

end TypeFree

theorem lFiveThompsonFieldInput_of_quot
    (hB : LFiveThompsonFieldQuotInput) : LFiveThompsonFieldInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀ x
    hxS hx2
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨hW₁Nt, -, -, -⟩ :=
    seitzTilde_fusion_facts hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  obtain ⟨hS₀p, hS₀N, hS₀syl, -, -⟩ := id hS₀
  have hW₁S₀ : W₁ ≤ S₀ := wOne_le_of_not_two_dvd_relIndex (IsPGroup.of_card hW₁c)
    (seitzTilde_le_normalizer W₁ Kc) hS₀p hS₀N hW₁Nt hS₀syl
  obtain ⟨v, hvS, hv⟩ := hB G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield
    S₀ hS₀ x hxS (by rw [hx2]; exact one_mem _)
  set w := v⁻¹ * (x * t) * v * t⁻¹ with hwdef
  have hwt : w * t = v⁻¹ * (x * t) * v := by rw [hwdef]; group
  have hw2 : w * t * (w * t) = 1 := by
    rw [hwt]
    calc v⁻¹ * (x * t) * v * (v⁻¹ * (x * t) * v) = v⁻¹ * (x * t * (x * t)) * v := by group
      _ = 1 := by rw [hx2]; group
  have hsurj := tcomm_surjective_of_card hW₁2 ht2 htN
    (by rw [hW₁c, card_wOne_inf_centralizer e hK hW₁t]; norm_num)
  obtain ⟨u, huW, hu⟩ := exists_conj_eq_of_mul_self_eq_one hW₁2 ht2 hsurj hv hw2
  refine ⟨v * u, mul_mem hvS (hW₁S₀ huW), ?_⟩
  calc x * t = v * (w * t) * v⁻¹ := by rw [hwt]; group
    _ = v * (u * t * u⁻¹) * v⁻¹ := by rw [hu]
    _ = v * u * t * (v * u)⁻¹ := by group

end CFSG.SeitzReduction.LinearPilot
