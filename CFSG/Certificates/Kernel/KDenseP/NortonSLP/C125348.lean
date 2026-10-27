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

#kc_plan CFSG.KD.SLP.c125348 "c125348.plan.txt" 33917 8618748797254601608
#kc_plan CFSG.KD.SLP.c125348 "c125348.grp.txt" 4832 16361155893974463537
#kc_select CFSG.KD.SLP.c125348 CH CH 210
#kc_select CFSG.KD.SLP.c125348 IXf IX 210
#kc_select CFSG.KD.SLP.c125348 PRf PR 165
#kc_select CFSG.KD.SLP.c125348 GKf GK 210
#kc_listDispatch CFSG.KD.SLP.c125348 WDb wd 32
#kc_listDispatch CFSG.KD.SLP.c125348 Gf G 30

namespace CFSG.KD.SLP.c125348

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 302 318

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 32))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 96 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 302 318 = true := by
  quickRfl

theorem ix : ((List.range 210).all fun k => Nat.blt (IXf k) 210) = true := by quickRfl

theorem plan : planOKP WL CHI 210 IT = true := by quickRfl

end CFSG.KD.SLP.c125348

#kc_each CFSG.KD.SLP.c125348.u 0 30

end
