module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125512 "c125512.plan.txt" 52495 7481870552460156312
#kc_plan CFSG.KD.SLP.c125512 "c125512.grp.txt" 6226 4333443084367954601
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX0.bin" 63707 9237968729287623889
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW0.bin" 65535 3787762857391583314
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX1.bin" 63707 17554802533076425233
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW1.bin" 65535 7295821776640192421
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX2.bin" 63703 6161372324108203686
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW2.bin" 65527 10126878832388496710
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX3.bin" 63707 10347868868576098983
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW3.bin" 65535 13632857713789358718
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX4.bin" 63707 9380755968507042675
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW4.bin" 65527 3837233366097300332
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX5.bin" 63703 16730979674612400978
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW5.bin" 65535 12866733738392799662
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX6.bin" 63707 4721310928847565585
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW6.bin" 65535 18245681959757982272
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX7.bin" 63703 15521527097371264415
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW7.bin" 65527 5940865493127718454
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX8.bin" 63703 699023746474325481
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW8.bin" 65535 15010666013454170260
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX9 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX9.bin" 63707 9386254816554060004
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW9 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW9.bin" 65527 3837233366097300332
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX10 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX10.bin" 63703 13462217650143050967
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW10 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW10.bin" 65535 6661168502847701890
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX11 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX11.bin" 63707 10239704654835321982
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW11 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW11.bin" 65535 767221663714240482
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX12 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX12.bin" 63703 14933966841572876771
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW12 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW12.bin" 65527 14811439320139034170
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX13 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX13.bin" 63703 13135196510120480446
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW13 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW13.bin" 65535 10563833983837883192
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RX14 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RX14.bin" 63707 16276509624673302756
#kc_repo #kc_natBin CFSG.KD.SLP.c125512 RW14 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125512_rec/RW14.bin" 65527 6384259831959905294
#kc_plan CFSG.KD.SLP.c125512 "c125512.rec.txt" 14480 8458388612827997983
#kc_select CFSG.KD.SLP.c125512 CH CH 255
#kc_select CFSG.KD.SLP.c125512 IXf IX 255
#kc_select CFSG.KD.SLP.c125512 PRf PR 228
#kc_select CFSG.KD.SLP.c125512 GKf GK 255
#kc_listDispatch CFSG.KD.SLP.c125512 WDb wd 20
#kc_listDispatch CFSG.KD.SLP.c125512 Gf G 36
#kc_select CFSG.KD.SLP.c125512 RXf RX 15
#kc_select CFSG.KD.SLP.c125512 RAf RA 15
#kc_select CFSG.KD.SLP.c125512 RWf RW 15

namespace CFSG.KD.SLP.c125512

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 332 342

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 20))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf S0 (nat_lit 18) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 60 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 332 342 = true := by
  quickRfl

theorem ix : ((List.range 255).all fun k => Nat.blt (IXf k) 255) = true := by quickRfl

theorem plan : planOKP WL CHI 255 IT = true := by quickRfl

end CFSG.KD.SLP.c125512

#kc_each CFSG.KD.SLP.c125512.u 0 36

end
