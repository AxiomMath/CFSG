module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionCentralProduct
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionDihedralProduct

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

theorem no_quasisimple_shape {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : CFSG.Open.IsQuasisimple A) (S₀ : Sylow 2 A) {t x ρ : G} {k : ℕ} (hk : 2 ≤ k)
    (htA : t ∈ normalizer (A : Set G)) (ht2 : t ^ 2 = 1)
    (htS : t ∈ normalizer (((S₀ : Subgroup A).map A.subtype : Subgroup G) : Set G))
    (hxS : x ∈ (S₀ : Subgroup A).map A.subtype) (hx : orderOf x = 4) (hxt : x * t = t * x)
    (hcent : ∀ s ∈ (S₀ : Subgroup A).map A.subtype, s * t = t * s → s ∈ zpowers x)
    (hρS : ρ ∈ (S₀ : Subgroup A).map A.subtype) (htρ : t * ρ * t⁻¹ = ρ⁻¹)
    (hρx : ρ * x = x * ρ) (hρo : orderOf ρ = 2 ^ k) (hρz : ρ ^ 2 ^ (k - 1) = x ^ 2)
    (hcard : Nat.card ((S₀ : Subgroup A).map A.subtype) = 2 ^ (k + 2)) : False := by
  have hs : Setting A S₀ t x ρ k :=
    ⟨hA, htA, ⟨hk, ht2, htS, hxS, hx, hxt, hcent, hρS, htρ, hρx, hρo, hρz, hcard⟩⟩
  by_cases hII : ∃ u ∈ (S₀ : Subgroup A).map A.subtype,
      u ∉ zpowers ρ ⊔ zpowers x ∧ u ^ 2 = 1
  · obtain ⟨u, huS, huM, hu2⟩ := hII
    rcases hs.config.conj_x huS with hux | hux
    · exact hs.false_of_caseIIb huS huM hu2 hux
    · exact hs.false_of_caseIIa huS huM hu2 hux
  · push Not at hII
    exact hs.false_of_caseI hII

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion
