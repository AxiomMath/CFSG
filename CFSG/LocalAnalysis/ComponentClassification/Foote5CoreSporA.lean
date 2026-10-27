module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_M11
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .M11) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_M11 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.at_m11_schreier.1.trans (by norm_num)))

theorem coreCondition_M12
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .M12) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_M12 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.at_m12_schreier.1.trans (by norm_num)))

theorem coreCondition_M22
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .M22) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_M22 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.at_m22_schreier.1.trans (by norm_num)))

theorem coreCondition_M23
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .M23) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_M23 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.at_m23_schreier.1.trans (by norm_num)))

theorem coreCondition_M24
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .M24) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_M24 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.at_m24_schreier.1.trans (by norm_num)))

theorem coreCondition_J1
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .J1) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer sporadicOddCoreFree_J1 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num)))

theorem coreCondition_J2
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .J2) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_J2 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.AT_J2_Schreier.1.trans (by norm_num)))

theorem coreCondition_J3
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .J3) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer CatalogueU.sporadicOddCoreFree_J3 ha hY θ
    (card_outer_le_of_mulEquiv θ (Sporadic.Schreier.AT_J3_Schreier.1.trans (by norm_num)))

end CFSG.ComponentClassification.Foote5
