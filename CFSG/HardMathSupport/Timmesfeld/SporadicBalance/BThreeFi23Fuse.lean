module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import Certificates.Certificate13654

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Residuals


theorem bThreeRc_holds : BThreeRc := Certificates.certificate13654.1

theorem bThreeRd_holds : BThreeRd := Certificates.certificate13654.2

end Residuals

section Main


theorem oPrimeCoreTrivialAt_B_three : OPrimeCoreTrivialAt 3 CFSG.Blueprint.NativeSporadic.B :=
  oPrimeCoreTrivialAt_B_three_of_fi23 bThreeRc_holds bThreeRd_holds

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
