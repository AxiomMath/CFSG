module

public import Certificates.Data.Kernel.NortonSLPK
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen7 "Gen7prog.plan.txt" 81295 13125527445379152710
#kc_listDispatch CFSG.KD.SLP.Gen7 CW c 349

namespace CFSG.KD.SLP.Gen7

@[expose] noncomputable def S : Array (CFSG.AGLEmbedding.Norton.ProdStep ×
    List CFSG.Monster.AxisCount.Native.Gen) := CFSG.KC.NortonSLPK.stepsC CW 349

end CFSG.KD.SLP.Gen7

end
