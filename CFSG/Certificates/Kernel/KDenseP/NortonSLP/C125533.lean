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

#kc_plan CFSG.KD.SLP.c125533 "c125533.plan.txt" 95949 12786340998147793591
#kc_plan CFSG.KD.SLP.c125533 "c125533.grp.txt" 17278 16586219272028303352
#kc_select CFSG.KD.SLP.c125533 CH CH 714
#kc_select CFSG.KD.SLP.c125533 IXf IX 714
#kc_select CFSG.KD.SLP.c125533 PRf PR 495
#kc_select CFSG.KD.SLP.c125533 GKf GK 714
#kc_listDispatch CFSG.KD.SLP.c125533 WDb wd 148
#kc_listDispatch CFSG.KD.SLP.c125533 Gf G 91

namespace CFSG.KD.SLP.c125533

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 70 144

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 148))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 444 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 70 144 = true := by
  quickRfl

theorem ix : ((List.range 714).all fun k => Nat.blt (IXf k) 714) = true := by quickRfl

theorem plan : planOKP WL CHI 714 IT = true := by quickRfl

end CFSG.KD.SLP.c125533

#kc_each CFSG.KD.SLP.c125533.u 0 91

end
