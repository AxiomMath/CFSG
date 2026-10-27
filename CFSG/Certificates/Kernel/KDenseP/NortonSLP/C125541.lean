module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.GenD13Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125541 "c125541.plan.txt" 8630 2112912840693812872
#kc_plan CFSG.KD.SLP.c125541 "c125541.grp.txt" 864 11918542799425406748
#kc_select CFSG.KD.SLP.c125541 CH CH 39
#kc_select CFSG.KD.SLP.c125541 IXf IX 39
#kc_select CFSG.KD.SLP.c125541 PRf PR 39
#kc_select CFSG.KD.SLP.c125541 GKf GK 39
#kc_listDispatch CFSG.KD.SLP.c125541 WDb wd 2
#kc_listDispatch CFSG.KD.SLP.c125541 Gf G 3

namespace CFSG.KD.SLP.c125541

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 396 397

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 2))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 6 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 396 397 = true := by
  quickRfl

theorem ix : ((List.range 39).all fun k => Nat.blt (IXf k) 39) = true := by quickRfl

theorem plan : planOKP WL CHI 39 IT = true := by quickRfl

end CFSG.KD.SLP.c125541

#kc_each CFSG.KD.SLP.c125541.u 0 3

end
