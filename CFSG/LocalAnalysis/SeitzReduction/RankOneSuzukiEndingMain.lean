module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiEnding
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiU

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint

@[expose] def SzC1ExclusionData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T : Subgroup G) (a : ℕ)
    (K : Type) [Field K] [Fintype K] [CharP K 2] (d : G) (u v : G → K) (κ : K)
    (R₂ U U₁ : Subgroup G), SzStart G L f t T → 1 ≤ a → f = 2 * a + 1 →
    Fintype.card K = 2 ^ f → d ∈ L → Odd (orderOf d) → SzRootCoords (szT₁ L T) a d u v κ →
    (∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) → SzR2 (szT₁ L T) R₂ t d →
    normalizer (szA L T t : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) →
    Nat.card (szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 3 →
    (szT₁ L T ⊔ R₂ ⊔ zpowers t) ⊓ centralizer ({t} : Set G) = T →
    (∀ x ∈ szT₁ L T, ∀ r ∈ R₂, x * r = r * x) →
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) →
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (R₂ : Set G) →
    SzU (szT₁ L T) R₂ t d (2 ^ f) U U₁ →
    (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) → False

theorem exists_szStart {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {f : ℕ} (hm : LieModel L .twistedB2 0 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (t : G) (T : Subgroup G), SzStart G L f t T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  have h2 : 2 ∣ Nat.card (centralizer (L : Set G)) := by
    have := Subgroup.card_subgroup_dvd_card (S₀ : Subgroup (centralizer (L : Set G)))
    rwa [hS2 S₀] at this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2 h2
  have ht : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe, hc]
  obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer ({(c : G)} : Set G))) := inferInstance
  refine ⟨c, (P : Subgroup _).map (centralizer ({(c : G)} : Set G)).subtype,
    ⟨hset, hm, ht, c.2, map_subtype_le _, P, ?_⟩⟩
  exact (comap_map_eq_self_of_injective (subtype_injective _) _).symm

section Main

theorem rankOneSuzukiExclusion_of_c1Data (hC1 : SzC1ExclusionData) : RankOneSuzukiExclusion := by
  intro G _ _ L hset f hm hS2
  obtain ⟨t, T, h⟩ := exists_szStart hset hm hS2
  obtain ⟨a, ha, hfa, K, _, _, _, hK, d, u, v, κ, hdL, hodd, hc, hκ, -, R₂, hR, hNR, hcard, hCR,
    hcomm, hN1, hN2, hSZG, U, U₁, hU⟩ := h.exists_szR2_szU
  by_cases hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹
  · by_cases hel : ∀ r ∈ R₂, r ^ 2 = 1
    · have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
      obtain ⟨b, hb, hb1⟩ := hc.exists_v_eq ha hKa 1
      obtain ⟨r, hr, hrb⟩ := hR.rho_surj b hb
      have hrr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hel r hr)
      have htr : t * r * t⁻¹ = r := by rw [hinv r hr, hrr]
      have hrt : r * t * r⁻¹ * t⁻¹ = 1 := by
        have e : r * t = t * r := by
          calc r * t = t * r * t⁻¹ * t := by rw [htr]
            _ = t * r := by group
        rw [e]
        group
      rw [hrt] at hrb
      rw [← hrb, hc.v_one] at hb1
      exact zero_ne_one hb1
    · push Not at hel
      exact hC1 G L f t T a K d u v κ R₂ U U₁ h ha hfa hK hdL hodd hc hκ hR hNR hcard hCR hcomm
        hN1 hN2 hU hinv hel
  · exact h.false_of_c0_of_card_sylow hS2 ha hfa hK hc hκ hR hU (hSZG hinv)

end Main

end CFSG.SeitzReduction.RankOne
