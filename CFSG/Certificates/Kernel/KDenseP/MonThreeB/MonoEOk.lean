module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.M3BM keyF key 415

namespace CFSG.KD.M3BME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.M3BM.keyF k) (CFSG.KD.M3BM.ents k)

end CFSG.KD.M3BME

end
