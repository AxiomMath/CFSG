module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_HS
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .HS) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_HS ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.SPOR.card_outer_HS_le_two.trans (by norm_num)))

theorem coreCondition_McL
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .McL) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_McL ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.McL_outer_card_le_two.1.trans (by norm_num)))

theorem coreCondition_Suz
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Suz) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_Suz ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.SuzOddCore.outer_carrier_suz.1.le.trans (by norm_num)))

theorem coreCondition_Ru
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Ru) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_Ru ha hY θ
    (card_outer_le_of_mulEquiv (θ.trans Sporadic.RuSchreier.ruEquivP)
      (Sporadic.RuSchreier.card_outer_ruP.le.trans (by norm_num)))

theorem coreCondition_Co3
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Co3) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer Sporadic.SmallOddCore.sporadicOddCoreFree_Co3 ha hY θ
    (card_outer_le_of_mulEquiv θ
      (RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le.trans (by norm_num)))

theorem coreCondition_Fi22
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Fi22) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_Fi22 ha hY θ
    (card_outer_le_of_mulEquiv θ
      (CatalogueOuterTwoPart.card_outer_fi22.le.trans (by norm_num)))

theorem coreCondition_Fi23
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Fi23) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_Fi23 ha hY θ
    (card_outer_le_of_mulEquiv θ
      (Sporadic.FischerOddCore.card_outer_fi23.le.trans (by norm_num)))

theorem coreCondition_Fi24Prime
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .Fi24Prime) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_Fi24Prime ha hY θ
    (card_outer_le_of_mulEquiv θ
      (Sporadic.Schreier.Fi24.card_outer_fi24prime.le.trans (by norm_num)))

end CFSG.ComponentClassification.Foote5
