module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.ONOddCore.ONan

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def ONanOuterCardLeTwo : Prop :=
  Nat.card (Outer (NativeSporadic.Carrier .ONan)) ≤ 2

variable {K : Type} [Group K] [Finite K]

theorem coreCondition_J4
    {a : K} (ha : orderOf a = 2) {Y : Subgroup K} (hY : IsPComponent 2 Y)
    (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .J4) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  (commutator_mono (commutator_self_le _) le_rfl).trans
    (coreCondition_of_sporadic_lift CatalogueU.sporadicOddCoreFree_J4
      (RankTwoSporadic.oddMultiplier_of_noPerfectDoubleCover
        RankTwoSporadic.J4.j4NoDoubleCover_checked) ha hY θ)

theorem coreCondition_ONan
    (hON : ONanOuterCardLeTwo) {a : K} (ha : orderOf a = 2) {Y : Subgroup K}
    (hY : IsPComponent 2 Y) (θ : Y ⧸ Open.fusionZStar Y ≃* NativeSporadic.Carrier .ONan) :
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K :=
  coreCondition_of_sporadic_outer Sporadic.ONOddCore.sporadicOddCoreFree_ONan ha hY θ
    (card_outer_le_of_mulEquiv θ (hON.trans (by norm_num)))

end CFSG.ComponentClassification.Foote5
