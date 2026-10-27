module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C2

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

@[expose] def DihedralConclusion : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {A : Subgroup G}, standardComponentOddCore G = ⊥ →
    standardComponentIsStandard A → ∀ {g : G}, g ∉ normalizer (A : Set G) →
    ∀ {R : Subgroup G}, IsSylowOf 2 R (centralizer (A : Set G)) → IsDihedralTwoGroup R →
    1 < Open.pRank 2 R →
    Nat.card R = 4 ∧ IsElemAbelian 2 R ∧ ∃ g' : G, g' ∉ normalizer (A : Set G) ∧
      ∃ T' : Subgroup G,
        IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) g' ⊓ normalizer (A : Set G)) ∧
          IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) g')

theorem asc76Theorem2_of_aux (h22 : Asc76Lemma22) (h75 : Asc75Theorem4) (h4' : Asc76Theorem4)
    (hU : UniqueOfInverts) (hD : DihedralConclusion) : Asc76Theorem2 := by
  intro G _ _ A hO hA hII hm R hR g hg T hT hT1
  by_cases hRd : IsDihedralTwoGroup R
  · exact Or.inl (hD hO hA hg hR hRd (one_lt_pRank_of_isSylowOf hR hm))
  · have hRe := isElemAbelian_of_not_isDihedralTwoGroup h22 h75 h4' hU hA hO hII hm hR hRd hg
    have hTs := isSylowOf_of_not_isDihedralTwoGroup h22 h75 h4' hU hA hO hII hm hR hRd hg hT hT1
    exact Or.inr ⟨hRe, hTs, commutator_inf_normalizer_eq_bot hA hR hRe hg hT hT1 hTs⟩

end CFSG.ComponentClassification.Asc76.Sec5
