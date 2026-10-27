module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporBasic

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_of_uBalanced_lift (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hK : SectionRank.IsKGroupCat K) {a : K} (ha : orderOf a = 2) {Y : Subgroup K}
    (hY : IsPComponent 2 Y) (hbal : UBalanced (Y ⧸ Open.fusionZStar Y))
    (hM : RankTwoSporadic.OddMultiplier (Y ⧸ Open.fusionZStar Y)) :
    ⁅oddCoreOfCentralizer a, Y⁆ ≤ pPrimeCore 2 K := by
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hcat : Blueprint.Catalog (Y ⧸ Open.fusionZStar Y) := hK Y (Open.fusionZStar Y) hsimple
  exact core_commutator_le_of_lift footeLBalanceInput_holds ha hY
    (odd_card_fusionZStar_of_oddMultiplier hY hM (MulEquiv.refl _))
    (hloc_of_coreFree hna (coreFree_of_uBalanced hU hcat hbal))

theorem coreCondition_of_uBalanced_outer (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hK : SectionRank.IsKGroupCat K) {a : K} (ha : orderOf a = 2) {Y : Subgroup K}
    (hY : IsPComponent 2 Y) (hbal : UBalanced (Y ⧸ Open.fusionZStar Y))
    (hout : Nat.card (OuterAutomorphisms.Outer (Y ⧸ Open.fusionZStar Y)) ≤ 8) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K := by
  obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
  have hcat : Blueprint.Catalog (Y ⧸ Open.fusionZStar Y) := hK Y (Open.fusionZStar Y) hsimple
  have : Finite (MulAut (Y ⧸ Open.fusionZStar Y)) :=
    Finite.of_injective _ (DFunLike.coe_injective (F := MulAut (Y ⧸ Open.fusionZStar Y)))
  exact core_commutator_le_of_outer_comm footeLBalanceInput_holds ha hY
    (hbal_of_coreFree hna (coreFree_of_uBalanced hU hcat hbal))
    (oddSubgroup_comm_of_card_le_eight hout)

end CFSG.ComponentClassification.Foote5
