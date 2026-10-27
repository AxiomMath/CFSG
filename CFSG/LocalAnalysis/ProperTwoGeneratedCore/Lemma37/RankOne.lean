module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneCaseII
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneCaseI

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def SquareCaseRankOneSwapOuterImpossible : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (H : Subgroup G) (z : G),
    SquareCaseSetting G S H z → ∀ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J →
      ¬ J ≤ escapingImage H z → (∀ x ∈ J, orderOf x = 2 → x = escapingBar z) →
      ∀ s ∈ escapingSylowImage S z, s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)) →
      ∀ w ∈ escapingSylowImage S z, w ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) →
        w ∉ J ⊔ J.map (MulAut.conj s).toMonoidHom → False

theorem squareCaseRankOneImpossible_of_swapOuter
    (hII : SquareCaseRankOneSwapOuterImpossible) :
    SquareCaseRankOneImpossible := by
  intro G _ _ S H z hsq J hJ hJH hJinv
  have h : RankOneSetting G S H z J := ⟨hsq, hJ, hJH, hJinv⟩
  by_cases hN : escapingSylowImage S z ≤ Subgroup.normalizer (J : Set (EscapingQuotient z))
  · have := h.normal_of_le_normalizer hN
    exact h.false_of_normal
  obtain ⟨s, hsS, hs⟩ := IsConcreteLE.not_le_iff_exists.mp hN
  by_cases hle : ∀ t ∈ escapingSylowImage S z,
      t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) → t ∈ J ⊔ swapComponent J s
  · exact h.false_of_swap_le_sup hsS hs hle
  · push Not at hle
    obtain ⟨w, hwS, hwN, hw⟩ := hle
    exact hII G S H z hsq J hJ hJH hJinv s hsS hs w hwS hwN hw

end CFSG.ProperTwoGeneratedCore.Lemma37
