module

public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBNoL3
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open CFSG.Monster.Generated CFSG.HardMathSupport.Solomon.Coordinator.YS08


theorem sporL3DownInner_M_of_census_gmat (hB2 : L3AutDvd) (hA : M3BCensusA) :
    SporL3DownInner .M :=
  sporL3DownInner_M_of_census CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
    (fun _ hs hinv => CFSG.HardMathSupport.Dickson.Sec6.BM.noL3Comp_gmat_of_invertedByTwoA hs hinv)
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.uninvertedOPrimeTrivial_gmat_of_twoAPureKlein
      Nat.prime_three (by norm_num)
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.oPrimeCoreTrivialAt_B_three
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat)
    hB2 hA

end CFSG.HardMathSupport.MathTwE6.M3BIrr
