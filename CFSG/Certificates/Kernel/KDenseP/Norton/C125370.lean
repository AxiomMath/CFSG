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
@[expose] def CFSG.KD.NRT.c125370.P : Prs := tri (tbActPairs tbB1 tbXRows tbC1 [6, 7, 8]) []

#kc_plan CFSG.KD.NRT.c125370 "c125370.plan.txt" 6084 12000623173535450493
#kc_plan CFSG.KD.NRT.c125370 "c125370.grp.txt" 4198 3178747810065980831
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX0.bin" 63703 15937113598124055215
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW0 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW0.bin" 65534 1191442343593238004
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX1.bin" 63703 6551241572224031905
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW1 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW1.bin" 65535 6140269941324759603
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX2.bin" 63703 5642275339168535892
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW2 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW2.bin" 65535 18035752479995991308
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX3.bin" 63703 14763758734968205631
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW3 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW3.bin" 65535 4957804695467014008
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX4.bin" 63707 7087187223326868254
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW4 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW4.bin" 65535 15799890656458179932
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX5.bin" 63703 15570207942578139871
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW5 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW5.bin" 65535 10328495065355573216
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX6.bin" 63707 7468424490223304648
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW6 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW6.bin" 65535 11412551805015468648
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX7.bin" 63703 7106267117841242999
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW7 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW7.bin" 65535 5405150591058486088
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX8.bin" 63707 8946387181625308198
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW8 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW8.bin" 65535 10203653354504454687
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX9.bin" 63707 394379695133021786
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW9 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW9.bin" 65535 2001132062128510870
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX10.bin" 63703 7415044771342775718
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW10 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW10.bin" 65535 12016875801714363030
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX11.bin" 63703 11335644336142969094
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW11 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW11.bin" 65535 60980851347779989
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX12.bin" 63707 14228359815469837764
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW12 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW12.bin" 65535 2874185741259337065
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX13.bin" 63699 15827668406112022703
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW13 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW13.bin" 65535 6534472128296344404
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX14.bin" 63703 4546744426358705640
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW14 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW14.bin" 65535 2475779571979587570
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX15.bin" 63703 15239937296489080041
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW15 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW15.bin" 65535 4096945838517011701
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX16.bin" 63703 14067404141040703717
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW16 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW16.bin" 65535 13049720972641974612
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX17.bin" 63707 4102763604356897713
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW17 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW17.bin" 65535 21271690914104399
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX18.bin" 63707 17617151001377863934
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW18 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW18.bin" 65535 1192340171945923813
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX19.bin" 63703 13723551182875245787
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW19 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW19.bin" 65535 11772225332829582242
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX20.bin" 63707 9958459680003213315
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW20 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW20.bin" 65535 8704496413291104419
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX21.bin" 63707 6833020667425066120
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW21 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW21.bin" 65535 6144494725850835122
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX22.bin" 63699 14930944944357189526
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW22 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW22.bin" 65535 17455826085619292204
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RX23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RX23.bin" 63703 18275933157140081649
#kc_repo #kc_natBin CFSG.KD.NRT.c125370 RW23 "CFSG/Certificates/Kernel/KDenseP/Norton/c125370_rec/RW23.bin" 65535 11309720530928529491
#kc_plan CFSG.KD.NRT.c125370 "c125370.rec.txt" 23173 4008163505823894349
#kc_select CFSG.KD.NRT.c125370 CH CH 168
#kc_select CFSG.KD.NRT.c125370 PRf PR 162
#kc_select CFSG.KD.NRT.c125370 GKf GK 168
#kc_listDispatch CFSG.KD.NRT.c125370 Gf G 33
#kc_select CFSG.KD.NRT.c125370 RXf RX 24
#kc_select CFSG.KD.NRT.c125370 RAf RA 24
#kc_select CFSG.KD.NRT.c125370 RWf RW 24

namespace CFSG.KD.NRT.c125370

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf S0 (nat_lit 27) g

end CFSG.KD.NRT.c125370

#kc_each CFSG.KD.NRT.c125370.u 0 33

end
