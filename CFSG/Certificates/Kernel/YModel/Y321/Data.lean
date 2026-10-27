module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM321C
public import CFSG.Certificates.Kernel.YModel.Texts.YM321P
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.Benes
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMY321 "CFSG/Certificates/Kernel/YModel/Y321/data/plan.items.gz" 105 1128519791208502620
  M0_[6] R0_[6] Z0_[6]

namespace CFSG.KD.YMY321

open CFSG.KC CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

#kc_benes CFSG.KD.YMY321 N 0 7 6 fun _ c => colPlanes (CFSG.KD.YM321P.F c) 32 56 6 0
#kc_select CFSG.KD.YMY321 Nf N 7

@[expose] noncomputable def T0_0 : Nat := N0
@[expose] noncomputable def T0_1 : Nat := N1
@[expose] noncomputable def T0_2 : Nat := N2
@[expose] noncomputable def T0_3 : Nat := N3
@[expose] noncomputable def T0_4 : Nat := N4
@[expose] noncomputable def T0_5 : Nat := N5
@[expose] noncomputable def T0_6 : Nat := N6
#kc_select CFSG.KD.YMY321 T0 T0_ 7
#kc_select CFSG.KD.YMY321 M0 M0_ 6
#kc_select CFSG.KD.YMY321 R0 R0_ 6
#kc_select CFSG.KD.YMY321 Z0 Z0_ 6
@[expose] noncomputable def WP0 (i : Nat) : Nat := CFSG.KD.YM321C.F (i + 1)
@[expose] noncomputable def WL0 (i : Nat) : Nat := lget CFSG.KD.YM321C.El (i + 1)

end CFSG.KD.YMY321

end
