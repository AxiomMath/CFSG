module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125007 "c125007.plan.txt" 53030 13950950282487686503
#kc_plan CFSG.KD.SLP.c125007 "c125007.grp.txt" 6515 7207754636198113144
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX0.bin" 63707 6917033855068334025
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW0.bin" 65523 14781196361305434646
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX1.bin" 63703 13757825114650295196
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW1.bin" 65535 15980393131350435309
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX2.bin" 63703 6008835091605723649
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW2.bin" 65535 16547596886161478124
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX3.bin" 63703 12544147687465373112
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW3.bin" 65523 14781196361305434646
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX4.bin" 63703 9964883910518374204
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW4.bin" 65535 5633008899180667459
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX5.bin" 63707 12529587714913619804
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW5.bin" 65535 18092086331023447453
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX6.bin" 63707 5620796741269042696
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW6.bin" 65523 8556175781401664023
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX7.bin" 63703 13807497719152173694
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW7.bin" 65535 14259281683197630041
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RX8.bin" 63707 9203881863111589711
#kc_repo #kc_natBin CFSG.KD.SLP.c125007 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125007_rec/RW8.bin" 65535 6548667396734927420
#kc_plan CFSG.KD.SLP.c125007 "c125007.rec.txt" 8685 8073405562455342042
#kc_select CFSG.KD.SLP.c125007 CH CH 264
#kc_select CFSG.KD.SLP.c125007 IXf IX 264
#kc_select CFSG.KD.SLP.c125007 PRf PR 234
#kc_select CFSG.KD.SLP.c125007 GKf GK 264
#kc_listDispatch CFSG.KD.SLP.c125007 WDb wd 22
#kc_listDispatch CFSG.KD.SLP.c125007 Gf G 42
#kc_select CFSG.KD.SLP.c125007 RXf RX 9
#kc_select CFSG.KD.SLP.c125007 RAf RA 9
#kc_select CFSG.KD.SLP.c125007 RWf RW 9

namespace CFSG.KD.SLP.c125007

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 311 322

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 22))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen13.chk WL) CH PRf Gf S0 (nat_lit 12) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 66 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 311 322 = true := by
  quickRfl

theorem ix : ((List.range 264).all fun k => Nat.blt (IXf k) 264) = true := by quickRfl

theorem plan : planOKP WL CHI 264 IT = true := by quickRfl

end CFSG.KD.SLP.c125007

#kc_each CFSG.KD.SLP.c125007.u 0 42

end
