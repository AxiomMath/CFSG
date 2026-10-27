module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22Assembly
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma33Proof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52OneProof
public import CFSG.HardMathSupport.Solomon.LocalBalance.UpsilonType
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_2Four
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511L34
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Lemma54
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Lemma510
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Lemma59
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop51Proof
public import CFSG.HardMathSupport.Solomon.Coordinator.L54Ext
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GJMain
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLMain

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem input19_2_4' : Input19_2_4 := fun G _ _ _ h1 h2 p hp hp2 B hB k hk h =>
  Coordinator.input19_2_4Pos_holds G h1
    (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.mpr
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 h2))
    p hp B hB k hk h

structure Sec5Inputs : Prop where
  l53b : Lemma53Ns.Input19_7_3b
  l53d : Lemma53Ns.Input9_5
  l53e : Lemma53Ns.Input9_2_8
  l53f : Lemma53Ns.Input14_5Aut
  l53g : Lemma53Ns.Input7_FieldInn
  l54a : CFSG.HardMathSupport.Solomon.Coordinator.Input23_16At3Ext
  l54b : Lemma54Ns.Input22_4
  l54d : Lemma54Ns.Input19_7_3d
  l54e : Lemma54Ns.Input7_FieldInnDiag
  l55a : Lemma55Ns.InputFieldAutTwo
  l55c : Lemma55Ns.Input23_26
  l55d : Lemma55Ns.Input14_5Three
  l210a : Lemma210Ns.Input11_2Struct
  l210b : Lemma210Ns.InputSylowCentreInn
  l58 : InputBZeroMaxS
  l59a : Lemma59Ns.InputONSylow
  l59b : Lemma59Ns.InputONAut
  l59c : Lemma59Ns.Input20_29
  l59g : Lemma59Ns.Gap_Final
  l510a : Lemma510Ns.Input6_1
  l510c : Lemma510Ns.Input7_L3Aut
  l510d : Lemma510Ns.Input14_5L3
  l510g1 : Lemma510Ns.Gap510_Nontrivial
  l510g2 : Lemma510Ns.Gap510_Type
  l510g3 : Lemma510Ns.Gap510_Centre
  l510g4 : Lemma510Ns.Gap510_Inner
  l510iia : Lemma510iiNs.Input19_7_Seitz
  l510iib : Lemma510iiNs.InputSL34Sylow
  l511a : Lemma511Ns.Input30_2
  l511b : Lemma511Ns.Input20_27_2
  l511c : Lemma511Ns.InputL3Center
  l511d : Lemma511Ns.InputL3FieldInner
  l511g3a : Lemma511L34Ns.InputL34AutInner
  l511g3b : Lemma511L34Ns.InputL34AutOuter
  l512a : Lemma512Ns.Input18_3
  l512b : Input25_3_512
  l512c : Lemma512Ns.InputSL3FieldFixed
  l512d : Lemma512Ns.InputSL3FieldRestrict
  l513 : Lemma513Ns.InputInnDiagStructure

theorem prop51_of_inputs {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I2 : Sec2Inputs i183 i112F) (I : Sec5Inputs)
    (gapK : Lemma510 → Lemma511Ns.Gap_KxType) (i271 : Input27_1K) (i116 : Input11_6)
    (hON : UniquenessMaximal.InputONGroup) : Prop51 := by
  have h52one : Lemma52One := lemma52One_of_input input19_2_4'
  have h31 : Lemma31 := lemma31_of_input27_1K i271
  have hFT := inputFeitThompson'
  have h24 := I2.lemma24
  have h33 : Lemma33 := lemma33_of_inputs i116 i183
  have h52 : Lemma52 := lemma52_of_input input19_2_4'
  have h53 : Lemma53 := lemma53_of_inputs h33 h31 i183 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds I.l53b CFSG.HardMathSupport.Solomon.Coordinator.input7_autQuotAbelian_holds I.l53d I.l53e
    I.l53f I.l53g (input3_3_ON_of_group hON)
  have h54 : Lemma54 := CFSG.HardMathSupport.Solomon.Coordinator.lemma54_of_inputs_ext I.l54a
    (CFSG.HardMathSupport.Solomon.Coordinator.upsilonExtremal_of_inputs
      (upsilonType_of_inputs h31 I2.i19_10 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds)
      (input3_3_ON_of_group hON)) I.l54b CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds I.l54d I.l54e
  have h55 : Lemma55 := lemma55_of_inputs hFT I.l55a (upsilonType_of_inputs h31 I2.i19_10 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds) I.l55c I.l55d
  have h210 : Lemma210 := lemma210_of_lemmas hFT lemma23_proved h24 I2.lemma26 I2.lemma27
    I2.lemma28 I2.lemma29 i112F I.l210a I.l210b
  have h56 : Lemma56 := lemma56_of_lemmas h210 h52 h53 h54 h55 i112F (upsilonType56_of_inputs h31 I2.i19_10 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds) (inputONNotIso_of_group hON)
  have h57 : Lemma57 := lemma57_of_lemma24_lemma56 h24 h56
  have h58 : Lemma58 := lemma58_of_inputs h57 I.l58
  have h59 : Lemma59 := lemma59_of_inputs h52one h53 h54 h58 h56 h31 I.l59a I.l59b I.l59c (inputONSimple_of_group hON)
    (inputONTypes_of_group hON) I2.i19_10 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_3_holds I.l59g
  have h510 : Lemma510 := lemma510_of_inputs h53 h56 h59 h31 I2.i19_10 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma510_holds I.l510a I.l510c
    i183 I.l510d I.l510g1 I.l510g2 I.l510g3 I.l510g4
  have h510ii : Lemma513Ns.Lemma510ii := lemma510ii_of_inputs h31 h59 h510 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds I.l510iia I.l510iib
  have h511 : Lemma511 := Lemma511Ns.lemma511_of_inputs h53 h56 h58 h510 I.l511a I.l511b I.l511c I.l511d
    (gapJStructure_of_lift (lemma510iiLift_of_inputs h31 h59 input19_1_2_lemma54_holds)) (gapK h510)
    (Lemma511L34Ns.gapL34_of_inputs h31 h59 CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma54_holds I.l511g3a I.l511g3b)
  have h512 : Lemma512 := lemma512_of_inputs_no38 h510 I.l512a I.l512b I.l512c I.l512d
  have h513 : Lemma513 := lemma513_of_inputs h53 h54 h55 h56 h510 h510ii h512 I.l513
  exact prop51_of_lemmas h52 h53 h54 h56 h510 h511 h513

end CFSG.HardMathSupport.Solomon.LocalBalance
