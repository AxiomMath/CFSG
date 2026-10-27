module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporThree
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporMathieu

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.Blueprint

set_option linter.unusedSectionVars false

@[expose] def openNames3' : Finset TauCeti.SporadicName := {.M12, .M22, .J4, .HS, .He}


theorem localTwoBalanceSporadicThree_of_open (hOne : SporadicOneParts)
    (hopen : ∀ name ∈ openNames3', SporadicTwoBalanceThree name) :
    LocalTwoBalanceSporadicThree := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  refine localTwoBalanceSporadicThree_of_open_names hOne fun name hname => ?_
  have hcls : name = .M11 ∨ name = .M23 ∨ name ∈ openNames3' := by
    unfold openNames3 at hname
    unfold openNames3'
    revert hname
    cases name <;> decide
  rcases hcls with rfl | rfl | h
  · exact sporadicTwoBalanceThree_M11 hbr hOut
  · exact sporadicTwoBalanceThree_M23 hbr hOut
  · exact hopen name h

end CFSG.HardMathSupport.Solomon.Coordinator
