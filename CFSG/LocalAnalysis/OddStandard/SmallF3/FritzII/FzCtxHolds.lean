module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AHolds
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzInputs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.OddStandard.SmallF3.HarrisU33 CFSG.ComponentClassification.StandardRecognition

theorem fritzCtxInput_holds :
    FritzCtxInput :=
  fun _ _ _ _ _ _ _ _ _ _ h0 h1 => ctxOfLemma4_1_holds h0 h1

end CFSG.OddStandard.SmallF3.FritzII
