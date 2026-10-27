module

public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Compat

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem native_rank_two_of_two_le_twoRank (hrank : 2 ≤ CFSG.Open.twoRank G) :
    TwoRankAtLeastTwo G := by
  obtain ⟨E, hE, hcard⟩ := CFSG.ComponentClassification.Helpers.twoRank_witness G
  have hfour : 4 ≤ Nat.card E := by
    rw [hcard]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hrank
  exact (twoRankAtLeastTwo_of_elementary_card_ge_four E hE hfour).map_of_injective
    E.subtype E.subtype_injective

theorem rank_two_quotient_of_odd (R : Subgroup G) [R.Normal]
    (hRodd : Odd (Nat.card R)) (hrank : TwoRankAtLeastTwo G) :
    TwoRankAtLeastTwo (G ⧸ R) := by
  obtain ⟨E, hcard, hsq⟩ := hrank
  have hE : IsElemAbelian 2 E := by
    refine ⟨CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one hsq, ?_⟩
    intro e he
    exact congrArg Subtype.val (hsq ⟨e, he⟩)
  have hrankE : TwoRankAtLeastTwo E :=
    twoRankAtLeastTwo_of_elementary_card_ge_four E hE hcard.ge
  exact hrankE.map_of_injective ((QuotientGroup.mk' R).domRestrict E)
    (odd_quotient_injective_on_elementary E R hE hRodd)

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
