module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Main
public import CFSG.LocalAnalysis.OddStandard.ThmCO2A8

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG.OddStandard.ThmC

theorem o2Structure_of_gor42 (hGor : Gor42) : O2Structure :=
  o2Structure_of_hyps hGor A8.a8Fact

end CFSG.OddStandard.ThmC.O2
