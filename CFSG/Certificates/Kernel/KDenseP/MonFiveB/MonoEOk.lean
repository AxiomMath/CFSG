module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.M5BM keyF key 561

namespace CFSG.KD.M5BME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.M5BM.keyF k) (CFSG.KD.M5BM.ents k)

end CFSG.KD.M5BME

end
