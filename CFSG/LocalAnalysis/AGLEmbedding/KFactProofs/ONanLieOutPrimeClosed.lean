module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutSThreeL2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutSThreeU3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutPspTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutG2Two

public section

namespace CFSG.AGLEmbedding

open CFSG.AGLEmbedding.LieOut

theorem lieOutInputs : LieOutInputs where
  psl_two := fun hp hp5 hx hxp hαinn _ h => lieOutConcl_psl_two_p hp hp5 hx hxp hαinn h
  psu_three := fun hp hp5 hx hxp hαinn _ h => lieOutConcl_psu_three_p hp hp5 hx hxp hαinn h
  psp_two := fun hp hp5 hx hxp hαinn _ h => lieOut_of_psp_two hp hp5 hx hxp hαinn h
  g2 := fun hp hp5 hx hxp hαinn _ h => lieOut_of_g2_two hp hp5 hx hxp hαinn h

theorem kFactLieOutPrime : KFactLieOutPrime := kFactLieOutPrime_of_inputs lieOutInputs

end CFSG.AGLEmbedding
