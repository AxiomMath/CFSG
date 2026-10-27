module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125510 "c125510.plan.txt" 38194 18423821300482831090
#kc_plan CFSG.KD.SLP.c125510 "c125510.grp.txt" 4741 7723256496043408771
#kc_select CFSG.KD.SLP.c125510 CH CH 198
#kc_select CFSG.KD.SLP.c125510 IXf IX 210
#kc_select CFSG.KD.SLP.c125510 PRf PR 165
#kc_select CFSG.KD.SLP.c125510 GKf GK 198
#kc_listDispatch CFSG.KD.SLP.c125510 WDb wd 24
#kc_listDispatch CFSG.KD.SLP.c125510 Gf G 33

namespace CFSG.KD.SLP.c125510

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 300 312

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 24))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 72 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 300 312 = true := by
  quickRfl

theorem ix : ((List.range 210).all fun k => Nat.blt (IXf k) 198) = true := by quickRfl

theorem plan : planOKP WL CHI 210 IT = true := by quickRfl

end CFSG.KD.SLP.c125510

#kc_each CFSG.KD.SLP.c125510.u 0 33

end
