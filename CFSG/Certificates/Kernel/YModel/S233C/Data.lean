module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM233F
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMS233C "CFSG/Certificates/Kernel/YModel/S233C/data/nets.items.gz" 441650 533053583534926356
  N[8] (U 8 47) GP[47] GL[47] TT0_[126] TT1_[64] TT2_[30] TT3_[12] TT4_[8] TT5_[2] TT6_[2]

namespace CFSG.KD.YMS233C

open CFSG.KC.YModel

#kc_select CFSG.KD.YMS233C Nf N 8
@[expose] noncomputable def U0 : Nat := N0
@[expose] noncomputable def U1 : Nat := N1
@[expose] noncomputable def U2 : Nat := N2
@[expose] noncomputable def U3 : Nat := N3
@[expose] noncomputable def U4 : Nat := N4
@[expose] noncomputable def U5 : Nat := N5
@[expose] noncomputable def U6 : Nat := N6
@[expose] noncomputable def U7 : Nat := N7
#kc_select CFSG.KD.YMS233C U U 47
#kc_select CFSG.KD.YMS233C GP GP 47
#kc_select CFSG.KD.YMS233C GL GL 47
#kc_select CFSG.KD.YMS233C TT0 TT0_ 126
#kc_select CFSG.KD.YMS233C TT1 TT1_ 64
#kc_select CFSG.KD.YMS233C TT2 TT2_ 30
#kc_select CFSG.KD.YMS233C TT3 TT3_ 12
#kc_select CFSG.KD.YMS233C TT4 TT4_ 8
#kc_select CFSG.KD.YMS233C TT5 TT5_ 2
#kc_select CFSG.KD.YMS233C TT6 TT6_ 2
@[expose] noncomputable def TT (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (TT6) TT5 (Nat.beq i 5)) TT4 (Nat.beq i 4)) TT3 (Nat.beq i 3)) TT2 (Nat.beq i 2)) TT1 (Nat.beq i 1)) TT0 (Nat.beq i 0)
@[expose] noncomputable def LF (c : Nat) : Nat := CFSG.KD.YM233F.F (CFSG.KC.YModel.lget [0, 1, 3, 4, 5, 6, 7, 8] c)

end CFSG.KD.YMS233C

end
