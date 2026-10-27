module

public import CFSG.Certificates.Kernel.KDenseP.Norton.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.NRTM keyF key 313

namespace CFSG.KD.NRTME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.NRTM.keyF k) (CFSG.KD.NRTM.ents k)

end CFSG.KD.NRTME

end
