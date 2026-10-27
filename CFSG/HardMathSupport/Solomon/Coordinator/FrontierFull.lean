module

public import CFSG.HardMathSupport.Solomon.Coordinator.Frontier
public import CFSG.HardMathSupport.Solomon.Coordinator.I33_4
public import CFSG.HardMathSupport.Solomon.Coordinator.OddTwoLocal
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Prop81
public import CFSG.HardMathSupport.Solomon.Coordinator.I713Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Dispatch
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Final

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem theoremOne_of_frontierFull
    (h21 : Prop21) (h22 : Prop22) (h31 : Lemma31) (h45 : CaseTwoFiveEven)
    (hIII : Prop42CaseThree) (h51 : Prop51) (h6 : Sec6Out) (i183 : Input18_3_4) (i25 : Input2_5)
    (i145 : Input14_5) (i252 : Input25_2) (i116 : Input11_6) (i18 : Input18_10) (i28 : Input28_8)
    (i10 : Input10_20_3) (iU : InputUExists) (i11 : Input11_3)
    (i5 : Input28_5) (it : InputMcLaughlinTypeFacts) : TheoremOne :=
  theoremOne_of_frontier' h21 h22 h31 h45 hIII
    (caseFourPreUniqueness_of_inputs i183 i25 i145 i252 i116 i18 i28 h51 h6)
    (prop81Core_of_inputs i_7_13_1_outerPPrime_holds i10 inputOddTwoLocal_proved input33_4_proved iU
      i11 i5 (input28_14_of_dispatch tvNormalizer_holds tvCentralized_holds) it)

end CFSG.HardMathSupport.Solomon.Coordinator
