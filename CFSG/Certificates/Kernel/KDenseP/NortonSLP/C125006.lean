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

#kc_plan CFSG.KD.SLP.c125006 "c125006.plan.txt" 60343 7309127911650880611
#kc_plan CFSG.KD.SLP.c125006 "c125006.grp.txt" 8675 18198387239786633453
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX0.bin" 63703 18143463269507595522
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW0.bin" 65535 1204947576020880614
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX1.bin" 63707 14062680444523761768
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW1.bin" 65535 10545387308501994619
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX2.bin" 63707 2173661135447067552
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW2.bin" 65535 1901319459742844657
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX3.bin" 63707 14551098787789543912
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW3.bin" 65535 1204947576020880614
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX4.bin" 63707 935045872718074541
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW4.bin" 65535 2149066593587674352
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX5.bin" 63707 7458753793696085665
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW5.bin" 65535 1007055265219387465
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX6.bin" 63703 10361426811708419667
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW6.bin" 65535 7592371017567067516
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX7.bin" 63707 5836777660567817552
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW7.bin" 65535 7146883735757111897
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RX8.bin" 63707 6748708706865436308
#kc_repo #kc_natBin CFSG.KD.SLP.c125006 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125006_rec/RW8.bin" 65535 9274287468268426996
#kc_plan CFSG.KD.SLP.c125006 "c125006.rec.txt" 8685 10587638409783417131
#kc_select CFSG.KD.SLP.c125006 CH CH 354
#kc_select CFSG.KD.SLP.c125006 IXf IX 354
#kc_select CFSG.KD.SLP.c125006 PRf PR 288
#kc_select CFSG.KD.SLP.c125006 GKf GK 354
#kc_listDispatch CFSG.KD.SLP.c125006 WDb wd 46
#kc_listDispatch CFSG.KD.SLP.c125006 Gf G 51
#kc_select CFSG.KD.SLP.c125006 RXf RX 9
#kc_select CFSG.KD.SLP.c125006 RAf RA 9
#kc_select CFSG.KD.SLP.c125006 RWf RW 9

namespace CFSG.KD.SLP.c125006

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 288 311

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 46))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen13.chk WL) CH PRf Gf S0 (nat_lit 12) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 138 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 288 311 = true := by
  quickRfl

theorem ix : ((List.range 354).all fun k => Nat.blt (IXf k) 354) = true := by quickRfl

theorem plan : planOKP WL CHI 354 IT = true := by quickRfl

end CFSG.KD.SLP.c125006

#kc_each CFSG.KD.SLP.c125006.u 0 51

end
