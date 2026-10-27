module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125349 "c125349.plan.txt" 55345 10471225655076409680
#kc_plan CFSG.KD.SLP.c125349 "c125349.grp.txt" 7461 10975734947253699456
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX0.bin" 63691 9625001137828632122
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW0.bin" 65535 6213234994907978748
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX1.bin" 63707 13320945081935440553
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW1.bin" 65527 7686173080696144489
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX2.bin" 63703 4985865355568941824
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW2.bin" 65534 7418374235492299032
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX3.bin" 63707 11738021392139950020
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW3.bin" 65535 6213234994907978748
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX4.bin" 63707 3667837381450313635
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW4.bin" 65527 7686173080696144489
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX5.bin" 63707 17342866420948725722
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW5.bin" 65534 4572163802964093701
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX6.bin" 63707 12419415791853165811
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW6.bin" 65535 3786181012405569459
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX7.bin" 63707 1038778674435114524
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW7.bin" 65527 17061262421193574791
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RX8.bin" 63707 13845028993534125105
#kc_repo #kc_natBin CFSG.KD.SLP.c125349 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125349_rec/RW8.bin" 65534 2137897611330664051
#kc_plan CFSG.KD.SLP.c125349 "c125349.rec.txt" 8685 11419175222789028090
#kc_select CFSG.KD.SLP.c125349 CH CH 306
#kc_select CFSG.KD.SLP.c125349 IXf IX 306
#kc_select CFSG.KD.SLP.c125349 PRf PR 255
#kc_select CFSG.KD.SLP.c125349 GKf GK 306
#kc_listDispatch CFSG.KD.SLP.c125349 WDb wd 36
#kc_listDispatch CFSG.KD.SLP.c125349 Gf G 45
#kc_select CFSG.KD.SLP.c125349 RXf RX 9
#kc_select CFSG.KD.SLP.c125349 RAf RA 9
#kc_select CFSG.KD.SLP.c125349 RWf RW 9

namespace CFSG.KD.SLP.c125349

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 318 336

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 36))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf S0 (nat_lit 12) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 108 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 318 336 = true := by
  quickRfl

theorem ix : ((List.range 306).all fun k => Nat.blt (IXf k) 306) = true := by quickRfl

theorem plan : planOKP WL CHI 306 IT = true := by quickRfl

end CFSG.KD.SLP.c125349

#kc_each CFSG.KD.SLP.c125349.u 0 45

end
