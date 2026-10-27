module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D17

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

@[expose] def B3Conclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (S : Subgroup G),
    Asc76Lemma22 → MinCounter Ω S → (∀ K ∈ Ω, ∀ J ∈ Ω, J ∈ dStarComp Ω K) →
    ∀ R : Subgroup G, R ∈ DSet Ω (sec4W Ω S) → ∀ z : G, IsZOf R z →
      (∀ T₁ ∈ DSet Ω (sec4W Ω S), ∀ T₂ ∈ DSet Ω (sec4W Ω S),
          ∃ m ∈ MGrp Ω (sec4W Ω S), T₂ = AschbacherTightEmbedding.rightConjugate T₁ m) ∧
        ({w | ∃ m ∈ MGrp Ω (sec4W Ω S), w = m⁻¹ * z * m} =
            omegaOne (sec4W Ω S) \ zZero Ω (sec4W Ω S) R z ∧
          ∀ x ∈ zZero Ω (sec4W Ω S) R z, ∀ m ∈ MGrp Ω (sec4W Ω S), m * x = x * m) ∧
        ∀ t ∈ normalizer (sec4W Ω S : Set G), t * t = 1 →
          ∃ m ∈ MGrp Ω (sec4W Ω S), t * (m⁻¹ * z * m) = m⁻¹ * z * m * t

theorem b3Conclusion_of_lemma411 (h : Lemma411) : B3Conclusion := by
  intro G _ _ Ω S h22 hM hconn R hR z hz
  exact h G Ω ⟨h22, hM.assumption, hM.twoNil⟩ S hM.sylow
    (hM.not_connected_commGraph h22 hconn) R hR z hz

end CFSG.ComponentClassification.Asc76.Sec4
