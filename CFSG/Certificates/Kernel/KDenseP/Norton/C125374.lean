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
@[expose] def CFSG.KD.NRT.c125374.P : Prs := tri (tbActPairs tbB2 tbYRows tbC2 [8, 9, 10, 11]) []

#kc_plan CFSG.KD.NRT.c125374 "c125374.plan.txt" 8286 12458189070190472556
#kc_plan CFSG.KD.NRT.c125374 "c125374.grp.txt" 5813 14700353212539927120
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX0.bin" 63703 9773252517231753667
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW0.bin" 65535 6505788107115042900
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX1.bin" 63707 6041350133498399575
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW1.bin" 65535 16083669690997656536
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX2.bin" 63707 7514750332501005555
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW2.bin" 65535 9293039913761331591
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX3.bin" 63703 2635557270272501462
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW3.bin" 65535 5424311129053686966
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX4.bin" 63707 9638405732867471449
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW4.bin" 65535 1118353312926139102
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX5.bin" 63707 9210939646913077974
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW5.bin" 65535 996851908929390130
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX6.bin" 63707 1190265015916859157
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW6.bin" 65535 15664916006021158322
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX7.bin" 63707 4236877374477352807
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW7.bin" 65535 12936021753145095438
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX8.bin" 63699 13835187445089795310
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW8.bin" 65535 11308885842801536888
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX9.bin" 63707 6186667259917044590
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW9.bin" 65535 1391121229960289049
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX10.bin" 63707 11757696013186250972
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW10.bin" 65535 2982989043480913289
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX11.bin" 63703 12569920287845392666
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW11.bin" 65535 1121589112026781880
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX12.bin" 63695 15804450931310600474
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW12.bin" 65535 1311017022593222867
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX13.bin" 63699 5670046511998286867
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW13.bin" 65535 14156338467445102850
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX14.bin" 63703 15354355453895074682
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW14.bin" 65535 17311938164776632550
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX15.bin" 63707 17968458211332484823
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW15.bin" 65535 10680096993605370380
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX16.bin" 63699 2768911462423116256
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW16.bin" 65535 16165449355189986856
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX17.bin" 63707 18407667535422646404
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW17.bin" 65535 398850883943556787
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX18.bin" 63703 16158991966068771
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW18.bin" 65535 13762441502421981980
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX19.bin" 63707 8297849392909986377
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW19.bin" 65535 1779579930098907553
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX20.bin" 63707 1982811421794198247
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW20.bin" 65535 8849506058306015289
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX21.bin" 63703 5603365008366593952
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW21.bin" 65535 16388633447941467954
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX22.bin" 63707 7527972531938272960
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW22.bin" 65535 14613715243226926792
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX23.bin" 63699 5852600622950535441
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW23.bin" 65535 7607113362835875128
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX24.bin" 63703 9353667371119921440
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW24 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW24.bin" 65535 10232097205306289391
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX25.bin" 63707 16136399962871879876
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW25 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW25.bin" 65535 2557572312250346339
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX26.bin" 63703 11644426758800899799
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW26 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW26.bin" 65535 14859506333422286403
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX27.bin" 63707 7812652068838602139
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW27 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW27.bin" 65535 11022118512265288248
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX28.bin" 63703 14750854865929844276
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW28 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW28.bin" 65535 1921217257741668201
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX29.bin" 63707 6967480559373641997
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW29 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW29.bin" 65535 11003908449856374259
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX30.bin" 63703 2678176465795623292
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW30 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW30.bin" 65535 10149745637705320139
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX31.bin" 63703 15156393531417223314
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW31 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW31.bin" 65535 7149593548813370902
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RX32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RX32.bin" 63707 10624804393194017941
#kc_repo #kc_natBin CFSG.KD.NRT.c125374 RW32 "CFSG/Certificates/Kernel/KDenseP/Norton/c125374_rec/RW32.bin" 65535 5789260602281235358
#kc_plan CFSG.KD.NRT.c125374 "c125374.rec.txt" 31867 15546091434646743504
#kc_select CFSG.KD.NRT.c125374 CH CH 228
#kc_select CFSG.KD.NRT.c125374 PRf PR 219
#kc_select CFSG.KD.NRT.c125374 GKf GK 228
#kc_listDispatch CFSG.KD.NRT.c125374 Gf G 45
#kc_select CFSG.KD.NRT.c125374 RXf RX 33
#kc_select CFSG.KD.NRT.c125374 RAf RA 33
#kc_select CFSG.KD.NRT.c125374 RWf RW 33

namespace CFSG.KD.NRT.c125374

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 36) g

end CFSG.KD.NRT.c125374

#kc_each CFSG.KD.NRT.c125374.u 0 45

end
