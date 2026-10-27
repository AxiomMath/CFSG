module

public import CFSG.HardMathSupport.Solomon.Coordinator.FrontierFull
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
public import CFSG.HardMathSupport.Solomon.Coordinator.TwoRankThree
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_5Holds
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Input113
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42Assembly
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop51Assembly
public import CFSG.HardMathSupport.Solomon.Proving.Fi22Facts
public import CFSG.HardMathSupport.Solomon.Coordinator.ONGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2Full
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Main
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.D4Two
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop21Assembly

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem theoremOne_of_localBalance_inputs
    (T112 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (TL2 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableL2)
    (TT : CFSG.HardMathSupport.Solomon.Coordinator.Tables112Types)
    (I2 : Sec2Inputs input18_3_4_holds
      (CFSG.HardMathSupport.Solomon.Coordinator.input11_2Full_of_tables T112 TL2 TT)) (I4 : Sec4Inputs) (I5 : Sec5Inputs)
    (gapK : Lemma510 → Lemma511Ns.Gap_KxType) (i271 : Input27_1K)
    (hD4 : CFSG.HardMathSupport.Timmesfeld.DefChar.DefCharInnerCoreFreeFamDFour)
    (hC : LocalThreeBalanceCrossChar) (hSp : LocalThreeBalanceSporadic)
    (h2 : LocalTwoBalanceGtFive)
    (h6 : Sec6Out) (i145 : Input14_5) (i252 : Input25_2) (i28 : Input28_8)
    (K116 : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.KernelT) : TheoremOne := by
  have h31 : Lemma31 := lemma31_of_input27_1K i271
  have h3 : LocalThreeBalance := localThreeBalance_of_simple_alt
    (localThreeBalanceSimple_of_families
      (CFSG.HardMathSupport.Timmesfeld.DefChar.localThreeBalanceDefChar_of_dFour hD4) hC hSp)
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.localThreeBalanceAlt_proved
  have h24 : Lemma24 := I2.lemma24
  have h43 : Lemma43 := lemma43_of_inputs CFSG.HardMathSupport.Solomon.Proving.fi22Facts_holds (input11_2_of_full (CFSG.HardMathSupport.Solomon.Coordinator.input11_2Full_of_tables T112 TL2 TT)) lemma23_proved (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_6_of_tables T112 K116) input18_3_4_holds
    I4.i14_20_7
  have h44 : Lemma44 := lemma44_of_inputs h31 h24
    (fun G _ _ _ h1 h2' p hp hp2 B hB k hk h =>
      Coordinator.input19_2_2Pos_holds G h1
        (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.mpr
          (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 h2'))
        p hp hp2 B hB k hk h) I2.i19_10
  have h22 : Prop22 := prop22_of_inputs I2
  exact theoremOne_of_frontierFull (prop21_of_localBalance CFSG.HardMathSupport.Timmesfeld.Balance.deltaOfLocalBalance_proved h3 h2) h22 h31
    (caseTwoFiveEvenGe5_of_lemmas h43 h44)
    (prop42CaseThree_of_inputs h31 h43 h44 h22 I4.i10_21 I4.i24_7 I4.i24_2 I4.uniq CFSG.HardMathSupport.Solomon.Coordinator.inputD4Two_holds)
    (prop51_of_inputs I2 I5 gapK i271
      (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_6_of_tables T112 K116)
      CFSG.HardMathSupport.Solomon.Coordinator.inputONGroup_holds) h6 input18_3_4_holds input2_5_proved i145 i252
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_6_of_tables T112 K116)
    input18_10_holds i28 input10_20_3_proved inputUExists_proved
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_3_of_tables T112 TL2)
    input28_5_holds inputMcLaughlinTypeFacts_holds

end CFSG.HardMathSupport.Solomon.LocalBalance
