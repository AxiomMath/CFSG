module

public import CFSG.Certificates.Kernel.KDenseP.M13.Run
public import CFSG.Certificates.Kernel.KDenseP.M13.PairsB
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

#kc_plan CFSG.KD.M13.c16958 "c16958.plan.txt" 11595 394386239894025846
#kc_plan CFSG.KD.M13.c16958 "c16958.grp.txt" 7805 4060925485867265191
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX0 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX0.bin" 63707 7407631623971166912
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW0 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW0.bin" 65535 14425632522281986610
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX1 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX1.bin" 63703 13546352881469892924
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW1 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW1.bin" 65535 9576111213909564590
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX2 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX2.bin" 63707 5111918661295036010
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW2 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW2.bin" 65535 17130854724405218214
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX3 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX3.bin" 63703 14598764032127644829
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW3 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW3.bin" 65535 5697276439579991558
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX4 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX4.bin" 63707 13966184755617009354
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW4 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW4.bin" 65535 17003524252380041174
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX5 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX5.bin" 63703 13546352881469892924
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW5 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW5.bin" 65535 9576111213909564590
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX6 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX6.bin" 63703 1895227519400990452
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW6 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW6.bin" 65535 9823454544787798033
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX7 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX7.bin" 63703 14598764032127644829
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW7 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW7.bin" 65535 5697276439579991558
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX8 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX8.bin" 63707 8648258883973424519
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW8 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW8.bin" 65535 3524088609704145503
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX9 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX9.bin" 63703 16220614920706085751
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW9 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW9.bin" 65535 3289631057816104234
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX10 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX10.bin" 63703 1546097157451894131
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW10 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW10.bin" 65535 8036649458578637026
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX11 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX11.bin" 63707 17074457603543958442
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW11 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW11.bin" 65535 6035159819375916827
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX12 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX12.bin" 63703 1660127117185817087
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW12 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW12.bin" 65535 15106828437327666450
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX13 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX13.bin" 63703 16220614920706085751
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW13 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW13.bin" 65535 3289631057816104234
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX14 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX14.bin" 63707 8820240963520137525
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW14 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW14.bin" 65535 8418402986254935118
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX15 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX15.bin" 63707 17074457603543958442
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW15 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW15.bin" 65535 6035159819375916827
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX16 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX16.bin" 63699 8106069579566514414
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW16 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW16.bin" 65535 9029241788661745465
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX17 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX17.bin" 63707 2549353386818122841
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW17 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW17.bin" 65535 6731837563771836274
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX18 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX18.bin" 63707 15321367865714783201
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW18 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW18.bin" 65535 12697532161703304007
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX19 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX19.bin" 63703 4627391177807605289
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW19 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW19.bin" 65535 4845443688678532382
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX20 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX20.bin" 63707 15103488541966492271
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW20 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW20.bin" 65535 17233869940475179047
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX21 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX21.bin" 63707 2549353386818122841
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW21 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW21.bin" 65535 6731837563771836274
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX22 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX22.bin" 63707 5682039430415354606
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW22 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW22.bin" 65535 293450443678718589
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RX23 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RX23.bin" 63703 4627391177807605289
#kc_repo #kc_natBin CFSG.KD.M13.c16958 RW23 "CFSG/Certificates/Kernel/KDenseP/M13/c16958_rec/RW23.bin" 65535 4845443688678532382
#kc_plan CFSG.KD.M13.c16958 "c16958.rec.txt" 23174 14062571820036710370
#kc_select CFSG.KD.M13.c16958 CH CH 315
#kc_select CFSG.KD.M13.c16958 PRf PR 270
#kc_select CFSG.KD.M13.c16958 GKf GK 315
#kc_listDispatch CFSG.KD.M13.c16958 Gf G 49
#kc_select CFSG.KD.M13.c16958 RXf RX 24
#kc_select CFSG.KD.M13.c16958 RAf RA 24
#kc_select CFSG.KD.M13.c16958 RWf RW 24

namespace CFSG.KD.M13.c16958

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.M13

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e16958 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e16958 [])) CH PRf Gf S0 (nat_lit 27) g

end CFSG.KD.M13.c16958

#kc_each CFSG.KD.M13.c16958.u 0 49

end
