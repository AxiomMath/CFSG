module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.MonoTab
public import Certificates.Data.Kernel.KDenseP.MonoBind
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_listDispatch CFSG.KD.M5RM keyF key 1488

namespace CFSG.KD.M5RME

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDenseP.monoEntOK CFSG.KD.KDF.F (CFSG.KD.M5RM.keyF k) (CFSG.KD.M5RM.ents k)

end CFSG.KD.M5RME

end
