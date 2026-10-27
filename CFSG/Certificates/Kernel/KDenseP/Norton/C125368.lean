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
@[expose] def CFSG.KD.NRT.c125368.P : Prs := tri (tbActPairs tbB1 tbXRows tbC1 [0, 1, 2]) []

#kc_plan CFSG.KD.NRT.c125368 "c125368.plan.txt" 7473 676827328016177684
#kc_plan CFSG.KD.NRT.c125368 "c125368.grp.txt" 5251 12745919275952548084
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX0.bin" 63703 9429270559153039048
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW0.bin" 65535 7368063173388506296
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX1.bin" 63699 468937929006084037
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW1.bin" 65535 4416884733293887442
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX2.bin" 63707 662207246948750157
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW2.bin" 65535 12999627803789475690
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX3.bin" 63707 15934549539605862123
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW3.bin" 65535 103427326149902555
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX4.bin" 63703 8963308453289724369
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW4.bin" 65535 14410649764886218352
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX5.bin" 63703 17805689616461430924
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW5.bin" 65535 8132428492424955896
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX6.bin" 63707 13441124706317800493
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW6.bin" 65535 3206151168953726771
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX7.bin" 63707 2154532756355378599
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW7.bin" 65535 2134531281730573101
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX8.bin" 63703 3819412765174744316
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW8.bin" 65535 3962334359415901800
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX9.bin" 63703 7641326082371494485
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW9.bin" 65535 6467850046800013395
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX10.bin" 63703 8897160064392337833
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW10.bin" 65535 5971972229344142200
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX11.bin" 63703 12543365302233379297
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW11.bin" 65535 15853630953085804042
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX12.bin" 63695 17204035567279609427
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW12.bin" 65535 7040544859541845833
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX13.bin" 63703 5312443683528002422
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW13.bin" 65535 17328809703068975126
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX14.bin" 63703 4406494868600867090
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW14.bin" 65535 10496020090765387818
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX15.bin" 63707 8224313625269411899
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW15.bin" 65535 5105057688038521383
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX16.bin" 63707 14744431121035300802
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW16.bin" 65535 11076191050663446531
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX17.bin" 63707 16237287568105648316
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW17.bin" 65535 12907666757724447891
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX18.bin" 63699 8581927722177109332
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW18.bin" 65535 5529626484436648998
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX19.bin" 63707 17816911589722136415
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW19.bin" 65535 11299375195187540145
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX20.bin" 63695 15584632376436362718
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW20.bin" 65535 18206396439075473923
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX21.bin" 63707 1315226796622240129
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW21.bin" 65535 17923141229121639521
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX22.bin" 63699 11979062082233100189
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW22.bin" 65535 7702951604068992208
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX23.bin" 63707 7240022903572129612
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW23.bin" 65535 14766965419992656815
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX24.bin" 63707 4177453679339130997
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW24.bin" 65535 18340219698944720273
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX25.bin" 63699 5724866462744603620
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW25.bin" 65535 11535344050432013467
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX26.bin" 63707 17492235923433864939
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW26.bin" 65535 4286482986478835767
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX27.bin" 63703 8077759959795931488
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW27.bin" 65535 15526203755099317878
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX28.bin" 63703 14987753426722574383
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW28.bin" 65535 11219267971347251588
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RX29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RX29.bin" 63707 15442435829803468064
#kc_repo #kc_natBin CFSG.KD.NRT.c125368 RW29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125368_rec/RW29.bin" 65535 17583249527849282084
#kc_plan CFSG.KD.NRT.c125368 "c125368.rec.txt" 28970 14494184840924621521
#kc_select CFSG.KD.NRT.c125368 CH CH 207
#kc_select CFSG.KD.NRT.c125368 PRf PR 201
#kc_select CFSG.KD.NRT.c125368 GKf GK 207
#kc_listDispatch CFSG.KD.NRT.c125368 Gf G 39
#kc_select CFSG.KD.NRT.c125368 RXf RX 30
#kc_select CFSG.KD.NRT.c125368 RAf RA 30
#kc_select CFSG.KD.NRT.c125368 RWf RW 30

namespace CFSG.KD.NRT.c125368

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 33) g

end CFSG.KD.NRT.c125368

#kc_each CFSG.KD.NRT.c125368.u 0 39

end
