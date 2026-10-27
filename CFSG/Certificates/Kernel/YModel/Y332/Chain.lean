module

public import CFSG.Certificates.Kernel.YModel.Y332.Data
public import CFSG.Certificates.Kernel.YModel.Texts.YM332C
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Benes

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMY332 "CFSG/Certificates/Kernel/YModel/Y332/data/plan.items.gz" 9657 10754323425329252469
  M0_[9] R0_[9] Z0_[9]

namespace CFSG.KD.YMY332

open CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def T0_0 : Nat := N0
@[expose] noncomputable def T0_1 : Nat := N1
@[expose] noncomputable def T0_2 : Nat := N2
@[expose] noncomputable def T0_3 : Nat := N3
@[expose] noncomputable def T0_4 : Nat := N4
@[expose] noncomputable def T0_5 : Nat := N5
@[expose] noncomputable def T0_6 : Nat := N6
@[expose] noncomputable def T0_7 : Nat := N7
@[expose] noncomputable def T0_8 : Nat := N8
@[expose] noncomputable def WP0 (i : Nat) : Nat := CFSG.KD.YM332C.F (i + 1)
@[expose] noncomputable def WL0 (i : Nat) : Nat := lget CFSG.KD.YM332C.El (i + 1)
#kc_benes CFSG.KD.YMY332 T0_ 9 12 15 fun T j =>
  netsApply 15 (wid 15) (repU (wid 15) 15) (wordNets 15 32 T (WP0 (j - 9)) (WL0 (j - 9))) (idP 15)
#kc_select CFSG.KD.YMY332 T0 T0_ 21
#kc_select CFSG.KD.YMY332 M0 M0_ 9
#kc_select CFSG.KD.YMY332 R0 R0_ 9
#kc_select CFSG.KD.YMY332 Z0 Z0_ 9

end CFSG.KD.YMY332

end
