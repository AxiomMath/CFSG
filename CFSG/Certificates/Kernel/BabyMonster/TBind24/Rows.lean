module

public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Data0
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BM.B64

open CFSG.KC.YModel

@[expose] noncomputable def TR24 (i : Nat) : Nat :=
  lget (lgetL CFSG.KC.BM.NativePair24.T.rows (Nat.div i 64)) (Nat.mod i 64)

end CFSG.KC.BM.B64

end
