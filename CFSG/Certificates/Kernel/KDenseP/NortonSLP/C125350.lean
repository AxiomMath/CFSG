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

#kc_plan CFSG.KD.SLP.c125350 "c125350.plan.txt" 51128 4174161715087622938
#kc_plan CFSG.KD.SLP.c125350 "c125350.grp.txt" 6489 12628748191049386782
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX0.bin" 63707 9947970444173624672
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW0.bin" 65531 5843093273068598493
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX1.bin" 63707 10242947416241215444
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW1.bin" 65535 12702084036655382346
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX2.bin" 63707 8667484219990573474
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW2.bin" 65535 10654409294942107782
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX3.bin" 63707 14878283827421384846
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW3.bin" 65531 5843093273068598493
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX4.bin" 63703 18113903632122374314
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW4.bin" 65535 12702084036655382346
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX5.bin" 63707 17580604370281252165
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW5.bin" 65535 15064026168624998860
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX6.bin" 63707 13823406532502081987
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW6.bin" 65535 12782446089569818192
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX7.bin" 63707 1178871566433671679
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW7.bin" 65535 2505231083643990752
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RX8.bin" 63707 5818014913048809436
#kc_repo #kc_natBin CFSG.KD.SLP.c125350 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125350_rec/RW8.bin" 65535 10654409294942107782
#kc_plan CFSG.KD.SLP.c125350 "c125350.rec.txt" 8685 6570604380884648784
#kc_select CFSG.KD.SLP.c125350 CH CH 267
#kc_select CFSG.KD.SLP.c125350 IXf IX 267
#kc_select CFSG.KD.SLP.c125350 PRf PR 231
#kc_select CFSG.KD.SLP.c125350 GKf GK 267
#kc_listDispatch CFSG.KD.SLP.c125350 WDb wd 26
#kc_listDispatch CFSG.KD.SLP.c125350 Gf G 39
#kc_select CFSG.KD.SLP.c125350 RXf RX 9
#kc_select CFSG.KD.SLP.c125350 RAf RA 9
#kc_select CFSG.KD.SLP.c125350 RWf RW 9

namespace CFSG.KD.SLP.c125350

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 336 349

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 26))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf S0 (nat_lit 12) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 78 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 336 349 = true := by
  quickRfl

theorem ix : ((List.range 267).all fun k => Nat.blt (IXf k) 267) = true := by quickRfl

theorem plan : planOKP WL CHI 267 IT = true := by quickRfl

end CFSG.KD.SLP.c125350

#kc_each CFSG.KD.SLP.c125350.u 0 39

end
