module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_Co1
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Co1) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_Co1 ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.SPOR.card_outer_Co1.le.trans (by norm_num)))

theorem coreCondition_Co2
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Co2) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer Sporadic.Co2Schreier.sporadicOddCoreFree_Co2 ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.SPOR.card_outer_Co2.le.trans (by norm_num)))

theorem coreCondition_HN
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .HN) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer Sporadic.HNOddCore.sporadicOddCoreFree_HN ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.SPOR.card_outer_HN.le.trans (by norm_num)))

theorem coreCondition_Ly
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Ly) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer Sporadic.LySchreier.sporadicOddCoreFree_Ly ha hY θ
    (card_outer_le_of_mulEquiv θ
      (by rcases RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> rw [h] <;> norm_num))

end CFSG.ComponentClassification.Foote5
