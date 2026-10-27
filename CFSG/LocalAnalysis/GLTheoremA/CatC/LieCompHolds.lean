module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Classical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3Export
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2Two
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Minus
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SuzukiReeTitsComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SymplecticOrthogonalComps
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4 CFSG.Open

section LieCompHolds


theorem lieComp_holds : LieComp.LieComp :=
  LieComp.lieComp_of_classical lieOrderBridge_holds YS08.LieQ.lieQConstrainedInner_three_holds
      (LieComp.d4OuterExport_holds (LieComp.trialityOddA2Comps_of_toral
          LieComp.TriA2.a2PlusComps_holds LieComp.TriA2.a2MinusComps_holds))
      (LieComp.lieCompOn_exceptional
          (LieComp.excRationalLieTypes_of_residualsD LieComp.excRationalLieTypesOuterD_proved
              LieComp.excRationalLieTypesF4Two_holds)
          (LieComp.trialityOuterExport_of (LieComp.trialityOddA2Comps_of_toral
              LieComp.TriA2.a2PlusComps_holds LieComp.TriA2.a2MinusComps_holds))
          (LieComp.excChar3Export_of_outer YS08.LieQ.lieQConstrainedInner_three_holds
              LieComp.excChar3OuterExport_holds))
      (LieComp.lieCompOn_suzukiReeTits
          (LieComp.reeG2Char3Export_of_lieQ lieOrderBridge_holds
              YS08.LieQ.lieQConstrainedInner_three_holds))

theorem lieCompsOn_holds {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ∀ F, LieComp.LieCompsOn p F
  | .linearUnitary => LieComp.lieCompsOn_linearUnitary hp (by omega)
  | .symplecticOrthogonal => LieComp.lieCompsOn_symplecticOrthogonal hp hp5
  | .exceptional =>
      LieComp.lieCompsOn_exceptional_of_outerD hp hp5 (LieComp.excRationalLieTypesOuterDP_proved hp)
  | .suzukiReeTits => LieComp.lieCompsOn_suzukiReeTits hp hp5

end LieCompHolds

section YS05Proved


theorem ys05_of_cat6_inputs_proved
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat6Inputs G p) : YS05 :=
  ys05_of_cat6_inputs lieComp_holds (fun _ hp hp5 => lieCompsOn_holds hp hp5)
    (fun _ hp hp2 => YS08.LieQ.lieQConstrainedInner_odd hp hp2) h

end YS05Proved

end CFSG.LocalAnalysis.GLTheoremA
