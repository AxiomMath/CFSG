module

public import CFSG.Certificates.Kernel.KDenseP.Norton.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13CheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ElevenCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenEligibleDefs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.Norton CFSG.AGLEmbedding.Norton.MON5_7 in
@[expose] def CFSG.KD.NRT.c125372.P : Prs := tri (tbActPairs tbB2 tbYRows tbC2 [0, 1, 2, 3]) []

#kc_plan CFSG.KD.NRT.c125372 "c125372.plan.txt" 4965 866373641459613718
#kc_plan CFSG.KD.NRT.c125372 "c125372.grp.txt" 3390 125144663499333828
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX0.bin" 63703 170099906818367900
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW0.bin" 65535 8796145799254070241
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX1.bin" 63707 2013860736362351245
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW1.bin" 65535 15305318442244741687
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX2.bin" 63707 1712559779761792440
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW2.bin" 65535 4918253497373320558
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX3.bin" 63703 2605782843891607986
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW3.bin" 65535 6979124344968225097
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX4.bin" 63707 3871567524111955853
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW4.bin" 65535 5180536586403675767
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX5.bin" 63703 2745618373238534574
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW5.bin" 65535 4504399775823239524
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX6.bin" 63703 16755636324798103950
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW6.bin" 65535 16755709560060381342
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX7.bin" 63703 16250574961130803502
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW7.bin" 65534 9518898447909384329
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX8.bin" 63707 14472975553147926224
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW8.bin" 65535 15643276179927384205
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX9.bin" 63707 14664973226795163427
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW9.bin" 65535 12030396439501372061
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX10.bin" 63703 10358457259763561271
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW10.bin" 65535 16786397832564739908
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RX11.bin" 63699 13524959337164548621
#kc_repo #kc_natBin CFSG.KD.NRT.c125372 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125372_rec/RW11.bin" 65535 14208948780388005067
#kc_plan CFSG.KD.NRT.c125372 "c125372.rec.txt" 11581 8585983704887123390
#kc_select CFSG.KD.NRT.c125372 CH CH 141
#kc_select CFSG.KD.NRT.c125372 PRf PR 132
#kc_select CFSG.KD.NRT.c125372 GKf GK 141
#kc_listDispatch CFSG.KD.NRT.c125372 Gf G 24
#kc_select CFSG.KD.NRT.c125372 RXf RX 12
#kc_select CFSG.KD.NRT.c125372 RAf RA 12
#kc_select CFSG.KD.NRT.c125372 RWf RW 12

namespace CFSG.KD.NRT.c125372

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 15) g

end CFSG.KD.NRT.c125372

#kc_each CFSG.KD.NRT.c125372.u 0 24

end
