module

public import CFSG.HardMathSupport.Solomon.Coordinator.PumpingUpLeaves
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvBAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvMAsm
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2LeafRep
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.AssemblyM
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2DownM
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.NoOrderSixtyFiveM
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownB
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2Two

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

set_option linter.unusedSectionVars false

theorem pumpingUpFacts_of_last_leaves
    (hM65 : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoOrder 65 CFSG.Blueprint.NativeSporadic.M)
    (hA2m : LieComp.A2MinusComps)
    (hD : LieComp.ExcRationalLieTypesOuterD) (hD5 : LieComp.ExcRationalLieTypesOuterDP 5) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts := by
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hSpM := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hR : ∀ name ∈ restNamesOpen, SporNoPumpup name := by
    intro name hname
    have : name = .B ∨ name = .M := by
      revert hname
      cases name <;> decide
    rcases this with rfl | rfl
    · exact sporNoPumpup_B_of_uninverted hSpM inputONGroup_holds hOut hbr B3B.hUB_holds
    · exact sporNoPumpup_M_of_uninverted hSpM inputONGroup_holds hOut B3B.hUM_holds
  exact pumpingUpFacts_of_leaves
    (CFSG.HardMathSupport.Dickson.Sec6.BM.sporL3DownInner_B_of_leaf
      CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
      (Dickson.Sec6.BM.b3BLeaf_of_rep
          CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.bThreeB_seven_free))
    CFSG.HardMathSupport.Dickson.Sec6.BM2.sporL3DownInner_M_holds
    hM65 hR nonD4LieContraOnF4TwoOdd_holds hD LieComp.excRationalLieTypesF4Two_holds
    (LieComp.trialityOddA2Comps_of_toral LieComp.TriA2.a2PlusComps_holds hA2m) hD5
    (LieComp.excRationalLieTypesF4SmallP_holds Nat.prime_five (by norm_num))

theorem pumpingUpFacts_of_lie_leaves
    (hA2m : LieComp.A2MinusComps)
    (hD : LieComp.ExcRationalLieTypesOuterD) (hD5 : LieComp.ExcRationalLieTypesOuterDP 5) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_last_leaves CFSG.HardMathSupport.Dickson.Sec6.I1431.noOrder65_M hA2m hD hD5

theorem pumpingUpFacts_holds
    : CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts :=
  pumpingUpFacts_of_lie_leaves LieComp.TriA2.a2MinusComps_holds
    (LieComp.excRationalLieTypesOuterDP_proved Nat.prime_three)
    (LieComp.excRationalLieTypesOuterDP_proved Nat.prime_five)

end CFSG.HardMathSupport.Solomon.Coordinator
