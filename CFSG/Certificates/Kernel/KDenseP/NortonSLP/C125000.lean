module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125000 "c125000.plan.txt" 78566 3736670285293896957
#kc_plan CFSG.KD.SLP.c125000 "c125000.grp.txt" 15537 7234918929781666004
#kc_select CFSG.KD.SLP.c125000 CH CH 645
#kc_select CFSG.KD.SLP.c125000 IXf IX 645
#kc_select CFSG.KD.SLP.c125000 PRf PR 447
#kc_select CFSG.KD.SLP.c125000 GKf GK 645
#kc_listDispatch CFSG.KD.SLP.c125000 WDb wd 134
#kc_listDispatch CFSG.KD.SLP.c125000 Gf G 84

namespace CFSG.KD.SLP.c125000

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 0 76

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 134))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 402 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 0 76 = true := by
  quickRfl

theorem ix : ((List.range 645).all fun k => Nat.blt (IXf k) 645) = true := by quickRfl

theorem plan : planOKP WL CHI 645 IT = true := by quickRfl

end CFSG.KD.SLP.c125000

#kc_each CFSG.KD.SLP.c125000.u 0 84

end
