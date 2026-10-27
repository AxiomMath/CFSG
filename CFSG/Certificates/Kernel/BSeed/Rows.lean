module

public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.BSeed

open CFSG.KC.YModel

@[expose] noncomputable def A1R (i : Nat) : Nat :=
  lget (lgetL CFSG.KC.BM.Seeds.A1.rows (Nat.div i 64)) (Nat.mod i 64)

@[expose] noncomputable def A2R (i : Nat) : Nat :=
  lget (lgetL CFSG.KC.BM.Seeds.A2.rows (Nat.div i 64)) (Nat.mod i 64)

end CFSG.KC.BSeed

end
