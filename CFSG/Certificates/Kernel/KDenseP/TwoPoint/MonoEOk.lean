module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.TPM keyF key 192

namespace CFSG.KD.TPME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.TPM.keyF k) (CFSG.KD.TPM.ents k)

end CFSG.KD.TPME

end
