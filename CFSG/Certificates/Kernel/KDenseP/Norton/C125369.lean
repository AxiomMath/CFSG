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
@[expose] def CFSG.KD.NRT.c125369.P : Prs := tri (tbActPairs tbB1 tbXRows tbC1 [3, 4, 5]) []

#kc_plan CFSG.KD.NRT.c125369 "c125369.plan.txt" 5715 7944089667429709286
#kc_plan CFSG.KD.NRT.c125369 "c125369.grp.txt" 3939 13879751317667640704
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX0.bin" 63703 5567027036340998514
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW0.bin" 65535 5313799273034770842
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX1.bin" 63703 11577954093567560522
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW1.bin" 65535 13213186432929250244
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX2.bin" 63707 4702553846778014445
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW2.bin" 65535 11886352535799543926
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX3.bin" 63707 5511578573900058909
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW3.bin" 65535 16323632248872170339
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX4.bin" 63707 5134824418573681589
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW4.bin" 65535 17227575295873402565
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX5.bin" 63707 689261349772770356
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW5.bin" 65535 8414248006000777826
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX6.bin" 63707 5037144625580081832
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW6.bin" 65535 16142284953198283825
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX7.bin" 63703 10909820986234780554
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW7.bin" 65535 12265810540351146379
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX8.bin" 63707 10955134134199955721
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW8.bin" 65535 4196008145780086259
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX9.bin" 63707 17662263747828026961
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW9.bin" 65535 17757285223825317455
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX10.bin" 63707 10806615285369160120
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW10.bin" 65535 6194023907925030111
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX11.bin" 63707 14213436733587807098
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW11.bin" 65535 7437174052649213517
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX12.bin" 63703 4035619052679595816
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW12.bin" 65535 5501428203278008951
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX13.bin" 63703 3802266586112509640
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW13.bin" 65535 8323172176267695141
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX14.bin" 63707 13727608449646715612
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW14.bin" 65535 17031734542061028844
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX15.bin" 63707 5117747297472039896
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW15.bin" 65535 8862662309127797337
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX16.bin" 63707 6297422000007403473
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW16.bin" 65534 17353391393684903385
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX17.bin" 63707 12705719082508219353
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW17.bin" 65535 2707915027241309409
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX18.bin" 63707 167742715213068607
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW18.bin" 65535 7929830617417911924
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX19.bin" 63707 4971349170204693000
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW19.bin" 65535 8222351215120402059
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RX20.bin" 63703 6644067370320243351
#kc_repo #kc_natBin CFSG.KD.NRT.c125369 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125369_rec/RW20.bin" 65535 111433396182513799
#kc_plan CFSG.KD.NRT.c125369 "c125369.rec.txt" 20275 6202407389620410682
#kc_select CFSG.KD.NRT.c125369 CH CH 159
#kc_select CFSG.KD.NRT.c125369 PRf PR 153
#kc_select CFSG.KD.NRT.c125369 GKf GK 159
#kc_listDispatch CFSG.KD.NRT.c125369 Gf G 30
#kc_select CFSG.KD.NRT.c125369 RXf RX 21
#kc_select CFSG.KD.NRT.c125369 RAf RA 21
#kc_select CFSG.KD.NRT.c125369 RWf RW 21

namespace CFSG.KD.NRT.c125369

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 24) g

end CFSG.KD.NRT.c125369

#kc_each CFSG.KD.NRT.c125369.u 0 30

end
