module

public import CFSG.Certificates.Kernel.KDense.Data.Tab

public section

namespace CFSG.KD.KDTE

@[expose] noncomputable def t (k : Nat) : Bool :=
  CFSG.KC.KDense.entryOK CFSG.KD.KDF.F CFSG.KD.KDT.T (CFSG.KD.KDT.T.arrs.getD k []) k

end CFSG.KD.KDTE

end
