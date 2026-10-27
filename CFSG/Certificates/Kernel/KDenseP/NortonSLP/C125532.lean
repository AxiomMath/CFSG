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

#kc_plan CFSG.KD.SLP.c125532 "c125532.plan.txt" 60053 10391296371694881927
#kc_plan CFSG.KD.SLP.c125532 "c125532.grp.txt" 9452 838762917643577995
#kc_select CFSG.KD.SLP.c125532 CH CH 393
#kc_select CFSG.KD.SLP.c125532 IXf IX 402
#kc_select CFSG.KD.SLP.c125532 PRf PR 288
#kc_select CFSG.KD.SLP.c125532 GKf GK 393
#kc_listDispatch CFSG.KD.SLP.c125532 WDb wd 72
#kc_listDispatch CFSG.KD.SLP.c125532 Gf G 60

namespace CFSG.KD.SLP.c125532

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 34 70

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 72))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 216 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 34 70 = true := by
  quickRfl

theorem ix : ((List.range 402).all fun k => Nat.blt (IXf k) 393) = true := by quickRfl

theorem plan : planOKP WL CHI 402 IT = true := by quickRfl

end CFSG.KD.SLP.c125532

#kc_each CFSG.KD.SLP.c125532.u 0 60

end
