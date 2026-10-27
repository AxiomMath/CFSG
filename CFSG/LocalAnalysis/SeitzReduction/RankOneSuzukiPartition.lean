module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiPartitionBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStart

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.Blueprint

namespace SzStart

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_conj_eq_mul_of_not_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) :
    ∃ b ∈ szA₁ (szT₁ L T), b ≠ 1 ∧ ∃ g : G, g⁻¹ * t * g = b * t := by
  obtain ⟨-, -, -, -, -, hZT, -, -, hnotA₁, -⟩ := h.facts_of_card_sylow hS2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyN, hyC⟩ := SzPartition.exists_mem_normalizer_not_mem_of_sylow h.le h.sylow hT
  have htZ : t ∈ T ⊓ centralizer (T : Set G) := by
    rw [hZT]
    exact mem_szA_right L T t
  have hs : y * t * y⁻¹ ∈ szA L T t := by
    rw [← hZT]
    exact conj_mem_inf_centralizer_of_mem_normalizer hyN htZ
  have hsA₁ : y * t * y⁻¹ ∉ szA₁ (szT₁ L T) := by
    simpa using hnotA₁ y⁻¹
  rcases SzPartition.mem_sup_zpowers_cases (centralizer_le (szA₁_le _) h.mem_centralizer_szT₁)
    h.sq_eq_one hs with h1 | ⟨b, hb, he⟩
  · exact absurd h1 hsA₁
  · refine ⟨b, hb, fun hb1 => hyC ?_, y⁻¹, by rw [inv_inv, he]⟩
    rw [hb1, one_mul] at he
    rw [mem_centralizer_singleton_iff]
    calc y * t = y * t * y⁻¹ * y := by group
      _ = t * y := by rw [he]

theorem partitionData_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) :
    SzPartitionData (szA₁ (szT₁ L T)) t := by
  obtain ⟨-, -, -, -, -, -, -, -, hnotA₁, hfus⟩ := h.facts_of_card_sylow hS2
  obtain ⟨a, ha, hfa, K, _, _, _, hK, d, u, v, κ, hdL, -, hc, -, hμ⟩ :=
    h.exists_torusCoords_of_card_sylow hS2
  have hKa : Fintype.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  exact ⟨h.sq_eq_one, centralizer_le (szA₁_le _) h.mem_centralizer_szT₁, hnotA₁, hfus,
    hc.torus_of_generator ha hKa hμ hdt, h.exists_conj_eq_mul_of_not_sylow hS2 hT⟩

theorem partition_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) :
    normalizer (szA L T t : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) ∧
    (gmsRootConjugates (szA L T t) (zpowers t)).ncard = 2 ^ f ∧
    (∀ a ∈ szA₁ (szT₁ L T), ∃ g : G, g⁻¹ * t * g = a * t) ∧
    ∀ Q₁ Q₂ Z₁ Z₂ : gmsRootConjugates (szA L T t) (zpowers t), Q₁ ≠ Q₂ → Z₁ ≠ Z₂ →
      ∃ σ ∈ (gmsRootConjugateAction (szA L T t) (zpowers t)).range, σ Q₁ = Z₁ ∧ σ Q₂ = Z₂ := by
  have hD := h.partitionData_of_card_sylow hS2 hT
  obtain ⟨-, -, -, hcardA₁, -⟩ := h.facts_of_card_sylow hS2
  exact ⟨hD.normalizer_le, hD.ncard_eq.trans hcardA₁, fun a ha => hD.exists_conj_eq ha,
    hD.two_transitive⟩

theorem action_eq_one_iff_of_card_sylow (h : SzStart G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hT : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T) (l : normalizer (szA L T t : Set G)) :
    gmsRootConjugateAction (szA L T t) (zpowers t) l = 1 ↔ (l : G) ∈ T := by
  obtain ⟨-, -, -, -, -, -, -, hCA, -⟩ := h.facts_of_card_sylow hS2
  refine ((h.partitionData_of_card_sylow hS2 hT).action_eq_one_iff l).trans ?_
  change (l : G) ∈ centralizer (szA L T t : Set G) ↔ (l : G) ∈ T
  rw [hCA]

theorem not_sylow
    (h : SzStart G L f t T) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
  not_exists_sylow_eq_suzuki_of_le_normalizer_zpowers h.setting h.model h.inv
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      h.setting.standardSetting.standard h.mem h.inv).1
    (h.le.trans (normalizer_zpowers_eq_centralizer_of_involution h.inv).ge)

end SzStart

end CFSG.SeitzReduction.RankOne
