module

public import Certificates.Data.Kernel.NortonSLPK
public import CFSG.Certificates.Kernel.Common.Chain
public import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_chain CFSG.KD.SLP.Gen13 "Gen13prog.plan.txt" 64852 16446458395401762768
#kc_listDispatch CFSG.KD.SLP.Gen13 CW c 322

namespace CFSG.KD.SLP.Gen13

@[expose] noncomputable def S : Array (CFSG.AGLEmbedding.Norton.ProdStep ×
    List CFSG.Monster.AxisCount.Native.Gen) := CFSG.KC.NortonSLPK.stepsC CW 322

end CFSG.KD.SLP.Gen13

end
