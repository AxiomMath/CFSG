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

#kc_plan CFSG.KD.SLP.c125511 "c125511.plan.txt" 64179 18045909423015764135
#kc_plan CFSG.KD.SLP.c125511 "c125511.grp.txt" 8511 9310537314438877451
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX0.bin" 63707 9129285373382970159
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW0 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW0.bin" 65535 1117782621731384441
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX1.bin" 63703 9499912954772663891
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW1 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW1.bin" 65535 3729783487528257200
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX2.bin" 63707 294715281233059502
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW2 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW2.bin" 65535 15853960673800978929
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX3.bin" 63703 13887297629296315652
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW3 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW3.bin" 65535 2998807311452316453
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX4.bin" 63707 7671401283885714994
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW4 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW4.bin" 65535 1117782621731384441
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX5.bin" 63703 16274658389077579144
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW5 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW5.bin" 65535 3729783487528257200
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX6.bin" 63703 12444982429808901281
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW6 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW6.bin" 65535 4245527123050478755
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX7.bin" 63707 1651126858333004743
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW7 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW7.bin" 65535 12999425076160778393
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX8.bin" 63707 3609552982360016864
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW8 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW8.bin" 65535 17625194332120846755
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX9 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX9.bin" 63703 272710701366981781
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW9 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW9.bin" 65535 9066832956826679356
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX10 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX10.bin" 63707 15573158715151454530
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW10 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW10.bin" 65535 4831995451226064350
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RX11 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RX11.bin" 63707 14390939949652262327
#kc_repo #kc_natBin CFSG.KD.SLP.c125511 RW11 "CFSG/Certificates/Kernel/KDenseP/NortonSLP/c125511_rec/RW11.bin" 65535 3269096631125905798
#kc_plan CFSG.KD.SLP.c125511 "c125511.rec.txt" 11582 8925642865353362687
#kc_select CFSG.KD.SLP.c125511 CH CH 345
#kc_select CFSG.KD.SLP.c125511 IXf IX 345
#kc_select CFSG.KD.SLP.c125511 PRf PR 288
#kc_select CFSG.KD.SLP.c125511 GKf GK 345
#kc_listDispatch CFSG.KD.SLP.c125511 WDb wd 40
#kc_listDispatch CFSG.KD.SLP.c125511 Gf G 49
#kc_select CFSG.KD.SLP.c125511 RXf RX 12
#kc_select CFSG.KD.SLP.c125511 RAf RA 12
#kc_select CFSG.KD.SLP.c125511 RWf RW 12

namespace CFSG.KD.SLP.c125511

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 312 332

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 40))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf S0 (nat_lit 15) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 120 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 312 332 = true := by
  quickRfl

theorem ix : ((List.range 345).all fun k => Nat.blt (IXf k) 345) = true := by quickRfl

theorem plan : planOKP WL CHI 345 IT = true := by quickRfl

end CFSG.KD.SLP.c125511

#kc_each CFSG.KD.SLP.c125511.u 0 49

end
