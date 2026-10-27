module

import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem u3l42_not_gamma_le {P' M : Subgroup G} {u : G} (huP : u ∈ P') (hu1 : u ≠ 1)
    (hu3 : u ^ 3 = 1) (hCu : ¬ centralizer ({u} : Set G) ≤ M) :
    ¬ rankThreeGamma 1 3 P' ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hle
  have hel : IsElemAbelian 3 (zpowers u) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
  have h1 : 1 ≤ CFSG.Open.pRank 3 (zpowers u) := le_pRank_of_elemAbelian_card le_rfl hel
    (by rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1, pow_one])
  have hCx : centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  apply hCu
  rw [← hCx]
  exact (Subgroup.centralizer_le_normalizer _).trans
    ((gamma_normalizer_le 1 3 P' (zpowers u) (zpowers_le.mpr huP) h1).trans hle)

omit [Finite G] in
theorem u3l42_decomp {T Z : Subgroup G} (hTZ : ∀ t ∈ T, ∀ c ∈ Z, t * c = c * t) {g : G}
    (hg : g ∈ T ⊔ Z) : ∃ t ∈ T, ∃ c ∈ Z, g = t * c := by
  have hTN : T ≤ normalizer (Z : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer (Z : Set G)
      (mem_centralizer_iff.mpr fun c hc => (hTZ t ht c hc).symm)
  have hg' : g ∈ ((T ⊔ Z : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T Z hTN] at hg'
  obtain ⟨t, ht, c, hc, rfl⟩ := hg'
  exact ⟨t, ht, c, hc, rfl⟩

omit [Finite G] in
theorem u3l42_commutator_mem {T Z : Subgroup G} (hTZ : ∀ t ∈ T, ∀ c ∈ Z, t * c = c * t)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) {a b : G} (ha : a ∈ T ⊔ Z) (hb : b ∈ T ⊔ Z) :
    ⁅a, b⁆ ∈ T := by
  obtain ⟨t₁, ht₁, c₁, hc₁, rfl⟩ := u3l42_decomp hTZ ha
  obtain ⟨t₂, ht₂, c₂, hc₂, rfl⟩ := u3l42_decomp hTZ hb
  have e1 : c₁ * t₂ = t₂ * c₁ := (hTZ t₂ ht₂ c₁ hc₁).symm
  have e2 : c₁ * c₂ = c₂ * c₁ := hZab c₁ hc₁ c₂ hc₂
  have e3 : c₂ * t₁ = t₁ * c₂ := (hTZ t₁ ht₁ c₂ hc₂).symm
  have e2' : c₁ * c₂ * c₁⁻¹ = c₂ := by rw [e2]; group
  have e3' : c₂ * t₁⁻¹ * c₂⁻¹ = t₁⁻¹ := by
    have h : c₂ * t₁⁻¹ = t₁⁻¹ * c₂ := (Commute.inv_right (show Commute c₂ t₁ from e3)).eq
    rw [h]; group
  have key : ⁅t₁ * c₁, t₂ * c₂⁆ = ⁅t₁, t₂⁆ := by
    calc ⁅t₁ * c₁, t₂ * c₂⁆
        = t₁ * (c₁ * t₂) * c₂ * (c₁⁻¹ * t₁⁻¹) * (c₂⁻¹ * t₂⁻¹) := by
          rw [commutatorElement_def]; group
      _ = t₁ * (t₂ * c₁) * c₂ * (c₁⁻¹ * t₁⁻¹) * (c₂⁻¹ * t₂⁻¹) := by rw [e1]
      _ = t₁ * t₂ * (c₁ * c₂ * c₁⁻¹) * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by group
      _ = t₁ * t₂ * c₂ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by rw [e2']
      _ = t₁ * t₂ * (c₂ * t₁⁻¹ * c₂⁻¹) * t₂⁻¹ := by group
      _ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by rw [e3']
      _ = ⁅t₁, t₂⁆ := by rw [commutatorElement_def]
  rw [key, commutatorElement_def]
  exact T.mul_mem (T.mul_mem (T.mul_mem ht₁ ht₂) (T.inv_mem ht₁)) (T.inv_mem ht₂)

end CFSG.LocalAnalysis.RankThreeTheoremC
