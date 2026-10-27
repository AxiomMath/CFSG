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

#kc_plan CFSG.KD.SLP.c125505 "c125505.plan.txt" 71858 15208972518119013550
#kc_plan CFSG.KD.SLP.c125505 "c125505.grp.txt" 12015 11861010616050487376
#kc_select CFSG.KD.SLP.c125505 CH CH 495
#kc_select CFSG.KD.SLP.c125505 IXf IX 498
#kc_select CFSG.KD.SLP.c125505 PRf PR 360
#kc_select CFSG.KD.SLP.c125505 GKf GK 495
#kc_listDispatch CFSG.KD.SLP.c125505 WDb wd 92
#kc_listDispatch CFSG.KD.SLP.c125505 Gf G 72

namespace CFSG.KD.SLP.c125505

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 33 79

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 92))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 276 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 33 79 = true := by
  quickRfl

theorem ix : ((List.range 498).all fun k => Nat.blt (IXf k) 495) = true := by quickRfl

theorem plan : planOKP WL CHI 498 IT = true := by quickRfl

end CFSG.KD.SLP.c125505

#kc_each CFSG.KD.SLP.c125505.u 0 72

end
