module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoverFiveScal

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Sporadic.Bridge.B

section

theorem sporadicCaseThreeData_B_of_tc (htc : TCGenDatum NativeSporadic.B 5) :
    SporadicCaseThreeDataRest :=
  sporadicCaseThreeData_B_of_tc_scal htc

end

end CFSG.AGLEmbedding
