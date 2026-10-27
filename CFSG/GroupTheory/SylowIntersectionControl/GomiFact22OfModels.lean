module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact22OfCore
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevBorelTitsHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalAltSixHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalExceptionalHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalReeF4Holds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalTitsHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalU33Holds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRadicalOfCases
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevSwapHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevHasBNHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevExcInvolutionHolds
public import CFSG.GroupTheory.SylowIntersectionControl.GomiBenderHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevFixedTypesOfBN
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorsSpHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorsSUHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorsSpinMinusHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorsSpinPlusHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviOfIsolated
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevRankOneOvergroupsHolds
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Overgroups
import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Assembly

public section

namespace CFSG.GroupTheory

open CFSG.Open

theorem gomiFact22_holds :
    GomiFact22 := by
  have hIso : GomiChevIsolated := gomiChevIsolated_of_gomiChevHasBN gomiChevBorelTits_holds
    gomiBender_holds gomiChevAtomOrbit_holds gomiChevSwap_holds (gomiChevRadical_of_cases
        LieType.ChevTwo.chevTwoModelSplit_holds
        chevParabolicRadicalSimple_of_chevalleyExceptionalModel
        chevParabolicRadicalSimple_of_lieModel_twistedF4 chevParabolicRadicalSimple_of_lieModel_tits
        chevParabolicRadicalSimple_of_mulEquiv_alt_six chevParabolicRadicalSimple_of_psu_three_three)
    CFSG.LieType.ChevTwo.chevTwoModelSplit_holds gomiChevHasBN_holds gomiChevExcInvolution_holds
  exact gomiFact22_of_parabolic hIso gomiChevBorelTits_holds gomiChevAtomGeneration_holds
    gomiChevAtomOrbit_holds (gomiChevRadical_of_cases LieType.ChevTwo.chevTwoModelSplit_holds
        chevParabolicRadicalSimple_of_chevalleyExceptionalModel
        chevParabolicRadicalSimple_of_lieModel_twistedF4 chevParabolicRadicalSimple_of_lieModel_tits
        chevParabolicRadicalSimple_of_mulEquiv_alt_six chevParabolicRadicalSimple_of_psu_three_three) gomiChevSwap_holds
    (gomiChevLevi_of_gomiChevIsolated hIso
      (gomiChevLeviDecomposition_holds gomiLeviFactorsSp_holds gomiLeviFactorsSU_holds
        gomiLeviFactorsSpinPlus_holds gomiLeviFactorsSpinMinus_holds
        GomiLeviExc.gomiLeviFactorsF4_holds GomiLeviExc.gomiLeviFactorsE6_holds
        GomiLeviExc.gomiLeviFactorsE7_holds GomiLeviExc.gomiLeviFactorsE8_holds
        GomiLeviExc.gomiLeviFactorsTwistedE6_holds)
      gomiChevRankOneOvergroups_holds gomiFact36Overgroups_holds)

end CFSG.GroupTheory
