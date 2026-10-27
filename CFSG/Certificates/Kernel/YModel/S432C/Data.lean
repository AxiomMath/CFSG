module

public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.YModel.Texts.YM432P
public import Certificates.Data.Kernel.YModel.Model
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Benes

public section

#kc_repo #kc_nat_items_gz CFSG.KD.YMS432C "CFSG/Certificates/Kernel/YModel/S432C/data/plan.items.gz" 8557 1742858536193051551
  GP[60] GL[60] TT0_[255] TT1_[126] TT2_[60] TT3_[24] TT4_[16] TT5_[8] TT6_[2] TT7_[2] TT8_[2]

namespace CFSG.KD.YMS432C

open CFSG.KC.YModel CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def LF (c : Nat) : Nat := CFSG.KD.YM432P.F (CFSG.KC.YModel.lget [0, 1, 2, 3, 4, 5, 6, 7, 8] c)
#kc_benes CFSG.KD.YMS432C N 0 9 15 fun _ c => colPlanes (LF c) 32 31671 15 0
#kc_select CFSG.KD.YMS432C Nf N 9
@[expose] noncomputable def U0 : Nat := N0
@[expose] noncomputable def U1 : Nat := N1
@[expose] noncomputable def U2 : Nat := N2
@[expose] noncomputable def U3 : Nat := N3
@[expose] noncomputable def U4 : Nat := N4
@[expose] noncomputable def U5 : Nat := N5
@[expose] noncomputable def U6 : Nat := N6
@[expose] noncomputable def U7 : Nat := N7
@[expose] noncomputable def U8 : Nat := N8
#kc_select CFSG.KD.YMS432C GP GP 60
#kc_select CFSG.KD.YMS432C GL GL 60
#kc_benes CFSG.KD.YMS432C U 9 51 15 fun T j =>
  netsApply 15 (wid 15) (repU (wid 15) 15) (wordNets 15 8 T (GP j) (GL j)) (idP 15)
#kc_select CFSG.KD.YMS432C U U 60
#kc_select CFSG.KD.YMS432C TT0 TT0_ 255
#kc_select CFSG.KD.YMS432C TT1 TT1_ 126
#kc_select CFSG.KD.YMS432C TT2 TT2_ 60
#kc_select CFSG.KD.YMS432C TT3 TT3_ 24
#kc_select CFSG.KD.YMS432C TT4 TT4_ 16
#kc_select CFSG.KD.YMS432C TT5 TT5_ 8
#kc_select CFSG.KD.YMS432C TT6 TT6_ 2
#kc_select CFSG.KD.YMS432C TT7 TT7_ 2
#kc_select CFSG.KD.YMS432C TT8 TT8_ 2
@[expose] noncomputable def TT (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (Bool.rec (motive := fun _ => Nat → Nat) (TT8) TT7 (Nat.beq i 7)) TT6 (Nat.beq i 6)) TT5 (Nat.beq i 5)) TT4 (Nat.beq i 4)) TT3 (Nat.beq i 3)) TT2 (Nat.beq i 2)) TT1 (Nat.beq i 1)) TT0 (Nat.beq i 0)

end CFSG.KD.YMS432C

end
