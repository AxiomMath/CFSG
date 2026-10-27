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

#kc_plan CFSG.KD.SLP.c125345 "c125345.plan.txt" 71774 2042566738848321074
#kc_plan CFSG.KD.SLP.c125345 "c125345.grp.txt" 12786 13251143951900303620
#kc_select CFSG.KD.SLP.c125345 CH CH 543
#kc_select CFSG.KD.SLP.c125345 IXf IX 543
#kc_select CFSG.KD.SLP.c125345 PRf PR 366
#kc_select CFSG.KD.SLP.c125345 GKf GK 543
#kc_listDispatch CFSG.KD.SLP.c125345 WDb wd 120
#kc_listDispatch CFSG.KD.SLP.c125345 Gf G 66

namespace CFSG.KD.SLP.c125345

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 174 234

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 120))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 360 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 174 234 = true := by
  quickRfl

theorem ix : ((List.range 543).all fun k => Nat.blt (IXf k) 543) = true := by quickRfl

theorem plan : planOKP WL CHI 543 IT = true := by quickRfl

end CFSG.KD.SLP.c125345

#kc_each CFSG.KD.SLP.c125345.u 0 66

end
