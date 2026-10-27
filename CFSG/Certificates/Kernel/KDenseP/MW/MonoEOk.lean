module

public import CFSG.Certificates.Kernel.KDenseP.MW.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.MWM keyF key 24

namespace CFSG.KD.MWME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.MWM.keyF k) (CFSG.KD.MWM.ents k)

end CFSG.KD.MWME

end
