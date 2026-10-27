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
@[expose] def CFSG.KD.NRT.c125371.P : Prs := tri (tbActPairs tbB1 tbXRows tbC1 [9, 10, 11]) []

#kc_plan CFSG.KD.NRT.c125371 "c125371.plan.txt" 7380 6817232660387001699
#kc_plan CFSG.KD.NRT.c125371 "c125371.grp.txt" 5174 17333886571235038056
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX0.bin" 63707 7808740166472371797
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW0.bin" 65535 7826508461717726090
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX1.bin" 63707 9345163682362453758
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW1.bin" 65535 4877178435008415673
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX2.bin" 63699 14788512454872200472
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW2.bin" 65535 12089850804130154242
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX3.bin" 63707 2632597280985943512
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW3.bin" 65535 6986812477293746956
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX4.bin" 63707 764781170585994802
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW4.bin" 65535 7319423159534549658
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX5.bin" 63703 9880520581434747650
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW5.bin" 65535 6607790470006168471
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX6.bin" 63703 6355576682386872567
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW6.bin" 65535 1582552506104773273
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX7.bin" 63703 9917692710036236941
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW7.bin" 65535 11709961807791040628
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX8.bin" 63707 12996661386943022543
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW8.bin" 65535 15298756948150339383
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX9.bin" 63703 9020677500972828660
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW9.bin" 65535 4344779551487361694
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX10.bin" 63707 5736999615376217479
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW10.bin" 65535 1263606427464776362
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX11.bin" 63707 11903521686229391589
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW11.bin" 65535 7439706598648875678
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX12.bin" 63707 6260217384691367742
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW12.bin" 65535 2084103972119000413
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX13.bin" 63707 3994957510032822556
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW13.bin" 65535 13706622695440542183
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX14.bin" 63707 7239933498845529909
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW14.bin" 65535 8429803568005527123
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX15.bin" 63707 16148806119712512537
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW15.bin" 65535 838390783265029611
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX16.bin" 63707 3905614326158930866
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW16.bin" 65535 14213136566568376346
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX17.bin" 63703 16834002960214212618
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW17.bin" 65535 15149813884647318065
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX18.bin" 63707 16168690296604851288
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW18.bin" 65535 3458377346332306536
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX19.bin" 63703 16981165069980127524
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW19.bin" 65535 15036451132273902688
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX20.bin" 63703 14790879587497696444
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW20.bin" 65535 5671906722495247756
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX21.bin" 63703 4064793708839212650
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW21.bin" 65535 6413493996217398222
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX22.bin" 63707 11489688925180427344
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW22.bin" 65535 6141648308047106882
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX23.bin" 63707 6117391389368129968
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW23.bin" 65535 13510045322721775352
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX24.bin" 63703 4403348937282825436
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW24.bin" 65535 5038706224258009315
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX25.bin" 63707 3756808656309655830
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW25.bin" 65535 9450787505781865442
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX26.bin" 63707 12590727314462617963
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW26.bin" 65535 6891692090140523040
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX27.bin" 63703 5989631727309610704
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW27.bin" 65535 17699672736145261395
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX28.bin" 63707 3824265439988691517
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW28.bin" 65534 2449942414294075512
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RX29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RX29.bin" 63707 14532554539699955410
#kc_repo #kc_natBin CFSG.KD.NRT.c125371 RW29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125371_rec/RW29.bin" 65535 4386618696153601077
#kc_plan CFSG.KD.NRT.c125371 "c125371.rec.txt" 28970 18266350705897749491
#kc_select CFSG.KD.NRT.c125371 CH CH 204
#kc_select CFSG.KD.NRT.c125371 PRf PR 198
#kc_select CFSG.KD.NRT.c125371 GKf GK 204
#kc_listDispatch CFSG.KD.NRT.c125371 Gf G 39
#kc_select CFSG.KD.NRT.c125371 RXf RX 30
#kc_select CFSG.KD.NRT.c125371 RAf RA 30
#kc_select CFSG.KD.NRT.c125371 RWf RW 30

namespace CFSG.KD.NRT.c125371

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 33) g

end CFSG.KD.NRT.c125371

#kc_each CFSG.KD.NRT.c125371.u 0 39

end
