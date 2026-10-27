module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen7Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.Gen7.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125342 "c125342.plan.txt" 42437 9770072734689219153
#kc_plan CFSG.KD.SLP.c125342 "c125342.grp.txt" 6626 6829659431618988515
#kc_select CFSG.KD.SLP.c125342 CH CH 285
#kc_select CFSG.KD.SLP.c125342 IXf IX 291
#kc_select CFSG.KD.SLP.c125342 PRf PR 210
#kc_select CFSG.KD.SLP.c125342 GKf GK 285
#kc_listDispatch CFSG.KD.SLP.c125342 WDb wd 52
#kc_listDispatch CFSG.KD.SLP.c125342 Gf G 42

namespace CFSG.KD.SLP.c125342

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 31 57

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 52))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 156 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 31 57 = true := by
  quickRfl

theorem ix : ((List.range 291).all fun k => Nat.blt (IXf k) 285) = true := by quickRfl

theorem plan : planOKP WL CHI 291 IT = true := by quickRfl

end CFSG.KD.SLP.c125342

#kc_each CFSG.KD.SLP.c125342.u 0 42

end
