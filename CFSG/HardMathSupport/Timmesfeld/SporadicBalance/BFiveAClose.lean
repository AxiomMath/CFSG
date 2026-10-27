module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveACover
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveA

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic


theorem bFiveNonCentral_holds : BFiveNonCentral :=
  bFiveNonCentral_of_twoBCover bFiveTwoBCover_holds

theorem oPrimeCoreTrivialAt_B_five : OPrimeCoreTrivialAt 5 B :=
  oPrimeCoreTrivialAt_B_five_of_twoBCover bFiveTwoBCover_holds

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
