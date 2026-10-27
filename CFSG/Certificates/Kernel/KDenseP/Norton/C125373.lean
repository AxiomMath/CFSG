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
@[expose] def CFSG.KD.NRT.c125373.P : Prs := tri (tbActPairs tbB2 tbYRows tbC2 [4, 5, 6, 7]) []

#kc_plan CFSG.KD.NRT.c125373 "c125373.plan.txt" 5421 4967875409155304685
#kc_plan CFSG.KD.NRT.c125373 "c125373.grp.txt" 3726 7625341115541476379
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX0.bin" 63707 13262368326180836204
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW0.bin" 65535 8538436659302208070
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX1.bin" 63707 7228161027609927788
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW1.bin" 65535 16301537767198356458
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX2.bin" 63703 534960654337464772
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW2.bin" 65535 15634695522130852033
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX3.bin" 63703 6056217080062494563
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW3.bin" 65535 1797684896620183504
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX4.bin" 63703 18191154960771140919
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW4.bin" 65535 2297139804433323728
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX5.bin" 63707 2291369905881707207
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW5.bin" 65535 16702958670032902208
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX6.bin" 63703 1320927420864906705
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW6.bin" 65535 656043362148989405
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX7.bin" 63707 12749851400262886941
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW7.bin" 65535 14520157692639831902
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX8.bin" 63703 9900662118262622448
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW8.bin" 65535 3186751897108402806
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX9.bin" 63703 13661818744218184963
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW9.bin" 65535 14487333635609524427
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX10.bin" 63707 4304249184562149650
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW10.bin" 65535 7436152846051959089
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX11.bin" 63699 16899260370892555429
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW11.bin" 65535 5952348261627573245
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX12.bin" 63703 12242821376925346939
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW12.bin" 65535 5765296744893172365
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX13.bin" 63703 1195195635434587123
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW13.bin" 65535 2590205192801435570
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RX14.bin" 63707 15785879908120134812
#kc_repo #kc_natBin CFSG.KD.NRT.c125373 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125373_rec/RW14.bin" 65535 3049985018911575942
#kc_plan CFSG.KD.NRT.c125373 "c125373.rec.txt" 14480 3962600101878039804
#kc_select CFSG.KD.NRT.c125373 CH CH 153
#kc_select CFSG.KD.NRT.c125373 PRf PR 144
#kc_select CFSG.KD.NRT.c125373 GKf GK 153
#kc_listDispatch CFSG.KD.NRT.c125373 Gf G 27
#kc_select CFSG.KD.NRT.c125373 RXf RX 15
#kc_select CFSG.KD.NRT.c125373 RAf RA 15
#kc_select CFSG.KD.NRT.c125373 RWf RW 15

namespace CFSG.KD.NRT.c125373

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 18) g

end CFSG.KD.NRT.c125373

#kc_each CFSG.KD.NRT.c125373.u 0 27

end
