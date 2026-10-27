module

public import Certificates.Data.Kernel.NortonSLPK
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.GenD13 "GenD13prog.plan.txt" 104550 6898988952982239642
#kc_listDispatch CFSG.KD.SLP.GenD13 CW c 397

namespace CFSG.KD.SLP.GenD13

@[expose] noncomputable def S : Array (CFSG.AGLEmbedding.Norton.ProdStep ×
    List CFSG.Monster.AxisCount.Native.Gen) := CFSG.KC.NortonSLPK.stepsC CW 397

end CFSG.KD.SLP.GenD13

end
