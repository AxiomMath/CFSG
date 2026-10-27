module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_Th
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Th) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer Sporadic.ThSchreier.sporadicOddCoreFree_Th ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.SPOR.card_outer_Th.le.trans (by norm_num)))

theorem coreCondition_B
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .B) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer BMCase.sporadicOddCoreFree_B ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.SPOR.card_outer_B.le.trans (by norm_num)))

theorem coreCondition_M
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .M) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_M ha hY θ
    (by
      obtain ⟨hsimple, -⟩ := zStarQuotient_simple hY
      exact (RankThree.PartOne.SPOR.card_outer_M_of_simple θ).le.trans (by norm_num))

end CFSG.ComponentClassification.Foote5
