module

public import CFSG.HardMathSupport.Solomon.Coordinator.PumpingUpLieQ
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3Export
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPFinal
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.BMNo65
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.ThThree
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co1
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co2
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co3
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi22
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi23
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Fi24
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.HN
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.J4
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Ly
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.McLON
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Suz
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Two

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

set_option linter.unusedSectionVars false


theorem sporL3DownInner_of_BM (hB : YS08.SporL3DownInner .B) (hM : YS08.SporL3DownInner .M) :
    ∀ s : TauCeti.SporadicName, YS08.SporL3DownInner s := by
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  intro s
  cases s with
  | M11 => exact YS08.sporL3DownInner_M11 hbr
  | M12 => exact YS08.sporL3DownInner_M12 hbr
  | M22 => exact YS08.sporL3DownInner_M22 hbr
  | M23 => exact YS08.sporL3DownInner_M23 hbr
  | M24 => exact YS08.sporL3DownInner_M24 hbr
  | J1 => exact YS08.sporL3DownInner_J1 hbr
  | J2 => exact YS08.sporL3DownInner_J2 hbr
  | J3 => exact YS08.sporL3DownInner_J3 hbr
  | J4 => exact YS08.sporL3DownInner_J4 hbr
  | HS => exact YS08.sporL3DownInner_HS hbr
  | McL => exact YS08.sporL3DownInner_McL hbr
  | He => exact YS08.sporL3DownInner_He hbr
  | Ru => exact YS08.sporL3DownInner_Ru hbr
  | Suz => exact YS08.sporL3DownInner_Suz hbr
  | ONan => exact YS08.sporL3DownInner_ONan hbr
  | Co1 => exact YS08.sporL3DownInner_Co1 hbr
  | Co2 => exact YS08.sporL3DownInner_Co2 hbr
  | Co3 => exact YS08.sporL3DownInner_Co3 hbr
  | Fi22 => exact YS08.sporL3DownInner_Fi22 hbr
  | Fi23 => exact YS08.sporL3DownInner_Fi23 hbr
  | Fi24Prime => exact YS08.sporL3DownInner_Fi24 hbr
  | HN => exact YS08.sporL3DownInner_HN hbr
  | Ly => exact YS08.sporL3DownInner_Ly hbr
  | Th => exact CFSG.HardMathSupport.Dickson.Sec6.th_sporL3DownInner hbr
  | B => exact hB
  | M => exact hM

theorem noOrderSixtyFiveBM_of_M
    (hM65 : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoOrder 65 CFSG.Blueprint.NativeSporadic.M) :
    NoOrderSixtyFiveBM := by
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hB65 : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoOrder 65
      (CFSG.Blueprint.NativeSporadic.Carrier .B) := by
    unfold CFSG.Blueprint.NativeSporadic.Carrier
    exact CFSG.HardMathSupport.Dickson.Sec6.I1431.noOrder65_B
  have hM65' : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoOrder 65
      (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
    unfold CFSG.Blueprint.NativeSporadic.Carrier
    exact hM65
  intro s hs g hg
  rcases hs with rfl | rfl
  · obtain ⟨e⟩ := hbr .B
    exact hB65 (e.symm g) (by rw [MulEquiv.orderOf_eq]; exact hg)
  · obtain ⟨e⟩ := hbr .M
    exact hM65' (e.symm g) (by rw [MulEquiv.orderOf_eq]; exact hg)

theorem pumpingUpFacts_of_leaves
    (hB : YS08.SporL3DownInner .B) (hM : YS08.SporL3DownInner .M)
    (hM65 : CFSG.HardMathSupport.Dickson.Sec6.I1431.NoOrder 65 CFSG.Blueprint.NativeSporadic.M)
    (hR : ∀ name ∈ restNamesOpen, SporNoPumpup name)
    (hF4 : NonD4LieContraOnF4TwoOdd)
    (hD : LieComp.ExcRationalLieTypesOuterD) (hF2 : LieComp.ExcRationalLieTypesF4Two)
    (hodd : LieComp.TrialityOddA2Comps)
    (hD5 : LieComp.ExcRationalLieTypesOuterDP 5) (hF5 : LieComp.ExcRationalLieTypesF4SmallP 5) :
    CFSG.Yardstones.M67c2c3e09a6b.PumpingUpFacts := by
  have hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hSpor : ∀ s, YS08.SporL3Down s := fun s =>
    YS08.sporL3Down_of_inner hOut (sporL3DownInner_of_BM hB hM s)
  have hres : LieComp.ExcRationalLieTypes := LieComp.excRationalLieTypes_of_residualsD hD hF2
  have hExc5 : LieComp.LieCompsOn 5 .exceptional :=
    LieComp.lieCompsOn_exceptional_of_two_residuals (by norm_num) le_rfl hD5 hF5
  have hLie : LieComp.LieComp :=
    LieComp.lieComp_of_classical lieOrderBridge_holds YS08.LieQ.lieQConstrainedInner_three_holds
        (LieComp.d4OuterExport_holds hodd)
        (LieComp.lieCompOn_exceptional hres (LieComp.trialityOuterExport_of hodd)
            (LieComp.excChar3Export_of_outer YS08.LieQ.lieQConstrainedInner_three_holds
                LieComp.excChar3OuterExport_holds))
        (LieComp.lieCompOn_suzukiReeTits
            (LieComp.reeG2Char3Export_of_lieQ lieOrderBridge_holds
                YS08.LieQ.lieQConstrainedInner_three_holds))
  exact pumpingUpFacts_of_open_residuals
    (input14_33TypeSameField_of_open hSpor
      (lieL3Down_of_lieComp hLie YS08.L3Char.l3CharUnique_holds) hF4)
    (noOrderSixtyFiveBM_of_M hM65) hR hres hodd LieComp.d4Char3Outer_holds
    LieComp.excChar3OuterExport_holds hExc5

end CFSG.HardMathSupport.Solomon.Coordinator
