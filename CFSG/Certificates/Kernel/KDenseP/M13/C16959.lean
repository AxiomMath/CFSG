module

public import CFSG.Certificates.Kernel.KDenseP.M13.Run
public import CFSG.Certificates.Kernel.KDenseP.M13.PairsA
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M13.c16959 "c16959.plan.txt" 4666 15810001736251483389
#kc_plan CFSG.KD.M13.c16959 "c16959.grp.txt" 2645 14840918017225536369
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RX0 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RX0.bin" 63703 8984674894464167987
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RW0 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RW0.bin" 65535 4826757415476682654
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RX1 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RX1.bin" 63707 13212097801282163491
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RW1 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RW1.bin" 65535 13888781385021996377
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RX2 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RX2.bin" 63707 16650616742113716269
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RW2 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RW2.bin" 65535 11279695882091687265
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RX3 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RX3.bin" 63707 5236096829855104133
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RW3 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RW3.bin" 65535 11980940488492545733
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RX4 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RX4.bin" 63703 2598581979462362226
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RW4 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RW4.bin" 65535 8273619113780412808
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RX5 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RX5.bin" 63703 5459236875492280022
#kc_repo #kc_natBin CFSG.KD.M13.c16959 RW5 "CFSG/Certificates/Kernel/KDenseP/M13/c16959_rec/RW5.bin" 65534 14322815807144284154
#kc_plan CFSG.KD.M13.c16959 "c16959.rec.txt" 5790 6991653878307664088
#kc_select CFSG.KD.M13.c16959 CH CH 123
#kc_select CFSG.KD.M13.c16959 PRf PR 96
#kc_select CFSG.KD.M13.c16959 GKf GK 123
#kc_listDispatch CFSG.KD.M13.c16959 Gf G 16
#kc_select CFSG.KD.M13.c16959 RXf RX 6
#kc_select CFSG.KD.M13.c16959 RAf RA 6
#kc_select CFSG.KD.M13.c16959 RWf RW 6

namespace CFSG.KD.M13.c16959

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.M13

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e16959 n16959) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e16959 n16959)) CH PRf Gf S0 (nat_lit 9) g

end CFSG.KD.M13.c16959

#kc_each CFSG.KD.M13.c16959.u 0 16

end
