module

public import Certificates.Data.Kernel.NortonSLPK
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen11 "Gen11prog.plan.txt" 87566 9894683861624545010
#kc_listDispatch CFSG.KD.SLP.Gen11 CW c 342

namespace CFSG.KD.SLP.Gen11

@[expose] noncomputable def S : Array (CFSG.AGLEmbedding.Norton.ProdStep ×
    List CFSG.Monster.AxisCount.Native.Gen) := CFSG.KC.NortonSLPK.stepsC CW 342

end CFSG.KD.SLP.Gen11

end
