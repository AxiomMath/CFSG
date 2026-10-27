module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Assembly
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Sporadic
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.OrthTwo
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Heisenberg
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4Inner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4Three
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4Five
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7Five
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7Four
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Five
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6Five
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4Four
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Residuals
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Four
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8Four

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator


theorem localTwoBalanceThreeFive_parts :
    LocalTwoBalanceCrossCharThree ∧ LocalTwoBalanceSporadicThree ∧
      LocalTwoBalanceCrossCharFive ∧ LocalTwoBalanceSporadicFive := by
  obtain ⟨h3, h5⟩ := Cross.localTwoBalanceCrossChar_three_five_of_rows
    Cross.psuTwoThreeBalance_holds Cross.spTwoThreeBalance_holds
    Cross.orthTwoThreeInnerBalance_holds (Cross.d4TrialityPlaneThreeBalance_of_coreFree
        Cross.d4TrialityCoreFree_holds)
    Cross.e6HeisenbergDiagThreeBalance_holds
    Cross.twistedE6HeisenbergDiagThreeBalance_holds Cross.triD4InnerThreeBalance_holds
    Cross.triD4OuterThreeBalance_holds Cross.reeF4InnerThreeBalance_holds
    Cross.reeF4InnerFiveBalance_holds Cross.e7InnerFiveOne_holds Cross.e7InnerFiveTwo_holds
    Cross.e7InnerFiveFour_holds Cross.e6InnerFiveOne_holds Cross.W2.e6InnerFiveFour_holds
    Cross.twistedE6InnerFiveTwo_holds Cross.W2.twistedE6InnerFiveFour_holds
    Cross.f4InnerFiveFour_holds Cross.e8InnerFiveFour_holds
  exact ⟨h3, localTwoBalanceSporadicThree_holds, h5, localTwoBalanceSporadicFive_holds⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
