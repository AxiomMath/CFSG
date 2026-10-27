module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylFour

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag

@[expose] def LFiveThompsonFieldInput : Prop :=
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
      ∀ x ∈ S₀, x * t * (x * t) = 1 → ∃ z ∈ S₀, x * t = z * t * z⁻¹

@[expose] def LFiveFieldSylowNormalInput : Prop :=
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
      ∀ g ∈ centralizer ({t} : Set G), g ∈ normalizer ((S₀ ⊔ zpowers t : Subgroup G) : Set G) →
        IsPGroup 2 (zpowers g) → g ∈ normalizer (S₀ : Set G)

@[expose] def LFiveGraphMcBrideInput : Prop :=
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
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      ∀ s ∈ normalizer ((S₀ ⊔ zpowers d ⊔ zpowers t : Subgroup G) : Set G),
        IsPGroup 2 (zpowers s) → s * t * s⁻¹ * d ∉ S₀ ∧ s * t * s⁻¹ * (d * t) ∉ S₀

theorem lFiveGraphSylowDataInput_of_inputs
    (hA : LFiveFieldSylowNormalInput) (hB : LFiveThompsonFieldInput)
    (hC : LFiveGraphMcBrideInput) : LFiveGraphSylowDataInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hconj := not_conj_mem_seitzTilde hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  obtain ⟨S₀, hS₀⟩ := exists_lFiveFieldSylow hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield
  obtain ⟨hS₀p, hS₀N, hS₀syl, htS₀, Q₀, hQL, hQc, hQS⟩ := id hS₀
  have hThom := hB G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨d, hdC, hdN₁, hdS, hdd, hdp⟩ := exists_graph_element hset hK e ht hKt hgraph c hW₁c
    hW₁2 hW₁t htN hLN hfield hS₀p hS₀N htS₀ hThom
  have hdS₀ : d ∈ normalizer (S₀ : Set G) :=
    hA G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀ d hdC hdN₁ hdp
  obtain ⟨hdQ, hdL, hdd'⟩ := graph_element_facts hset hK e ht hKt c hW₁t htN Kc hS₀p hS₀N htS₀
    hQL hQc hQS hdC hdN₁ hdS hdd
  rcases hdd' with hdd2 | hdd4
  swap
  · exact (false_of_mul_self_mul_mem hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield hS₀p hS₀N
      htS₀ hQL hQc hQS hThom hdC hdS₀ hdS hdd4).elim
  have hdt : d * t = t * d := mem_centralizer_singleton_iff.1 hdC
  have hdata : IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d :=
    ⟨hS₀p, hS₀N, hS₀syl, htS₀, hdS₀, hdt, hQS hdd2, outer_of_not_mem_sup hKt hdC hdL⟩
  refine ⟨S₀, d, hdata, ?_⟩
  set S : Subgroup G := S₀ ⊔ zpowers d ⊔ zpowers t with hSdef
  have htN' : t ∈ normalizer ((S₀ ⊔ zpowers d : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_mem_of_mem_normalizer htS₀ (mem_normalizer_zpowers_of_mul_eq_mul hdt)
  have hSp : IsPGroup 2 S :=
    isPGroup_sup_zpowers_of_mem_normalizer (isPGroup_sup_zpowers_of_mul_self_mem hS₀p hdS₀
      (hQS hdd2)) htN' (isPGroup_zpowers_two_of_mul_self ht2)
  have hle : Q₀ ⊔ zpowers t ⊔ zpowers d ≤ S :=
    sup_le (sup_le (hQS.trans (le_sup_left.trans le_sup_left)) le_sup_right)
      (le_sup_right.trans le_sup_left)
  have hmax := maximal_inf_centralizer hset hK e ht hKt hQL hQc hdC hdQ
    (fun h => hdS (sup_le_sup_right hQS _ h)) (mem_sup_left hdd2) hle
  have hodd : ¬ 2 ∣ S.index := by
    refine not_two_dvd_index_of_forall_conj hSp hmax fun s hsN hsp => ?_
    have hyS : s * t * s⁻¹ ∈ S := (mem_normalizer_iff.1 hsN t).1 (mem_sup_right (mem_zpowers t))
    obtain ⟨hC1, hC2⟩ :=
      hC G L hset K hK e t ht hKt hgraph c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ d hS₀ hdata s
        hsN hsp
    rcases mem_or_of_mem_sup_zpowers_sup_zpowers htS₀ hdS₀ hdt (hQS hdd2) ht2 hyS with
      h | h | h | h
    · exact absurd (hS₀N h) (by simpa using hconj s⁻¹)
    · have h3 : s * t * s⁻¹ * t * t = s * t * s⁻¹ := by rw [mul_assoc _ t t, ht2, mul_one]
      have hy2 : s * t * s⁻¹ * (s * t * s⁻¹) = 1 := by
        calc s * t * s⁻¹ * (s * t * s⁻¹) = s * (t * t) * s⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      obtain ⟨z, hzS₀, hz⟩ := hThom _ h (by rw [h3]; exact hy2)
      rw [h3] at hz
      exact ⟨z, mem_sup_left (mem_sup_left hzS₀), hz⟩
    · exact absurd h hC1
    · exact absurd h hC2
  exact mem_normalizer_or_of_not_two_dvd_index hS₀p (hS₀N.trans (seitzTilde_le_normalizer W₁ Kc))
    htN htS₀ hdS₀ hdt (hQS hdd2) ht2 hodd

end CFSG.SeitzReduction.LinearPilot
