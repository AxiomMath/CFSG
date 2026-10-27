module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

section Seven


theorem b3SporPair_B_seven
    (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .B 7 := by
  haveI : Finite (NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  exact b3SporPair_of_model_prime (by norm_num) (by norm_num) hOut (NativeSporadic.Carrier .B)
    (hbr .B) fun x hx => b3Phi_of_card_le_two (BSeven.oPrimeCoreLeTwoAt_B_seven x hx)

end Seven

end CFSG.HardMathSupport.Solomon.Coordinator
