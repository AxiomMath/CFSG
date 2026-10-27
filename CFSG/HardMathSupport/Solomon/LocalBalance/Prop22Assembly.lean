module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Part3
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_1Lemma25
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma26
public import CFSG.HardMathSupport.Solomon.LocalBalance.I253Consumers
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem inputFeitThompson' : InputFeitThompson := fun _ _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h

structure Sec2Inputs (i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4) (i112F : Input11_2Full) : Prop where
  i19_10 : Input19_10
  i19_5_2 : Input19_5_2
  l25a : Lemma25Ns.Input11_2_2
  l25c : Lemma25Ns.Input19_6_9
  l25d : Lemma25Ns.Input14_3_L3
  l26 : Lemma26Ns.Input11_2One
  l27a : Lemma27Ns.Input30_2
  l27b : Input25_3_27
  l27c : Lemma27Ns.Input14_5
  l27d : Lemma27Ns.Input11_2Four
  l27e : Lemma27Ns.Input11_2Two
  l27f : Lemma27Ns.InputB0T
  l27g : Lemma27Ns.Input14_33
  l27h : Lemma27Ns.InputD4
  l28a : Input23_26
  l28b : Input18_2One
  l28c : Input14_5Second

namespace Sec2Inputs

theorem lemma24 {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Lemma24 :=
  lemma24_of_inputs lemma23_proved I.i19_10 CFSG.HardMathSupport.Solomon.Coordinator.input19_3_1_holds i112F I.i19_5_2

theorem lemma25 {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Lemma25Strong :=
  lemma25_of_inputs I.lemma24 i183 I.l25a CFSG.HardMathSupport.Solomon.Coordinator.input19_1_2_lemma25_holds I.l25c I.l25d

theorem lemma26 {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Lemma26Plus :=
  lemma26plus_of_inputs I.lemma24 I.lemma25 I.l26

theorem lemma27 {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Lemma27 :=
  lemma27_of_inputs_no38 I.lemma24 I.lemma25 i112F I.l27d I.l27e I.l27f I.l27a i183 I.l27c
    I.l27b I.l27g I.l27h

theorem lemma28 {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Lemma28 :=
  lemma28_of_inputs I.lemma24 I.l28a I.l28b I.l28c

theorem lemma29 {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Lemma29 :=
  lemma29_of_input11_2 (input11_2_of_full i112F)

end Sec2Inputs

theorem prop22_of_inputs {i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4} {i112F : Input11_2Full} (I : Sec2Inputs i183 i112F) : Prop22 :=
  prop22_of_lemmas inputFeitThompson' I.lemma24 I.lemma26 I.lemma27 I.lemma28 I.lemma29

end CFSG.HardMathSupport.Solomon.LocalBalance
