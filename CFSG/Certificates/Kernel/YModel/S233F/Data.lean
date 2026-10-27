module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM233F
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMS233F "CFSG/Certificates/Kernel/YModel/S233F/data/nets.items.gz" 429373 12702149612951295131
  N[9] (U 9 36) GP[36] GL[36] TT0_[3510] TT1_[2816] TT2_[567] TT3_[120] TT4_[24] TT5_[2] TT6_[2]

namespace CFSG.KD.YMS233F

open CFSG.KC.YModel

#kc_select CFSG.KD.YMS233F Nf N 9
@[expose] noncomputable def U0 : Nat := N0
@[expose] noncomputable def U1 : Nat := N1
@[expose] noncomputable def U2 : Nat := N2
@[expose] noncomputable def U3 : Nat := N3
@[expose] noncomputable def U4 : Nat := N4
@[expose] noncomputable def U5 : Nat := N5
@[expose] noncomputable def U6 : Nat := N6
@[expose] noncomputable def U7 : Nat := N7
@[expose] noncomputable def U8 : Nat := N8
#kc_select CFSG.KD.YMS233F U U 36
#kc_select CFSG.KD.YMS233F GP GP 36
#kc_select CFSG.KD.YMS233F GL GL 36
#kc_select CFSG.KD.YMS233F TT0 TT0_ 3510
#kc_select CFSG.KD.YMS233F TT1 TT1_ 2816
#kc_select CFSG.KD.YMS233F TT2 TT2_ 567
#kc_select CFSG.KD.YMS233F TT3 TT3_ 120
#kc_select CFSG.KD.YMS233F TT4 TT4_ 24
#kc_select CFSG.KD.YMS233F TT5 TT5_ 2
#kc_select CFSG.KD.YMS233F TT6 TT6_ 2
@[expose] noncomputable def TT (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (TT6) TT5 (Nat.beq i 5)) TT4 (Nat.beq i 4)) TT3 (Nat.beq i 3)) TT2 (Nat.beq i 2)) TT1 (Nat.beq i 1)) TT0 (Nat.beq i 0)
@[expose] noncomputable def LF (c : Nat) : Nat := CFSG.KD.YM233F.F (CFSG.KC.YModel.lget [0, 1, 2, 3, 4, 5, 6, 7, 8] c)

end CFSG.KD.YMS233F

end
