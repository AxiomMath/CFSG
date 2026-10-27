module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125539 "c125539.plan.txt" 65784 4370797554822034844
#kc_plan CFSG.KD.SLP.c125539 "c125539.grp.txt" 9053 13987429685708795558
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX0.bin" 63703 9759271574088196105
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW0.bin" 65535 9152562593232208614
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX1.bin" 63707 17150414010045433823
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW1.bin" 65535 3728896687371670286
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX2.bin" 63707 11743241914439920338
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW2.bin" 65535 10790228576267635669
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX3.bin" 63707 13238732829881753312
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW3.bin" 65527 6813991193115698278
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX4.bin" 63707 1584612303118096807
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW4.bin" 65535 11065707504521811172
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX5.bin" 63703 7623248727746881323
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW5.bin" 65535 3728896687371670286
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX6.bin" 63707 5925695204616392043
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW6.bin" 65535 7076368395660555302
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX7.bin" 63707 364521169414931355
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW7.bin" 65535 13077943650111076656
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX8.bin" 63707 7283371799971082723
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW8.bin" 65535 2113758713733695903
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX9 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX9.bin" 63707 8685427474042130241
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW9 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW9.bin" 65535 3728171811375137538
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX10 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX10.bin" 63707 4482546244695692194
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW10 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW10.bin" 65535 5474249043275694126
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RX11 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RX11.bin" 63707 3265832774962504693
#kc_repo #kc_natBin CFSG.KD.SLP.c125539 RW11 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125539_rec/RW11.bin" 65535 6130787667522433250
#kc_plan CFSG.KD.SLP.c125539 "c125539.rec.txt" 11581 6070599150960662888
#kc_select CFSG.KD.SLP.c125539 CH CH 369
#kc_select CFSG.KD.SLP.c125539 IXf IX 369
#kc_select CFSG.KD.SLP.c125539 PRf PR 303
#kc_select CFSG.KD.SLP.c125539 GKf GK 369
#kc_listDispatch CFSG.KD.SLP.c125539 WDb wd 46
#kc_listDispatch CFSG.KD.SLP.c125539 Gf G 48
#kc_select CFSG.KD.SLP.c125539 RXf RX 12
#kc_select CFSG.KD.SLP.c125539 RAf RA 12
#kc_select CFSG.KD.SLP.c125539 RWf RW 12

namespace CFSG.KD.SLP.c125539

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 354 377

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 46))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf S0 (nat_lit 15) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 138 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 354 377 = true := by
  quickRfl

theorem ix : ((List.range 369).all fun k => Nat.blt (IXf k) 369) = true := by quickRfl

theorem plan : planOKP WL CHI 369 IT = true := by quickRfl

end CFSG.KD.SLP.c125539

#kc_each CFSG.KD.SLP.c125539.u 0 48

end
