module

public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.AXM keyF key 2663

namespace CFSG.KD.AXME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.AXM.keyF k) (CFSG.KD.AXM.ents k)

end CFSG.KD.AXME

end
