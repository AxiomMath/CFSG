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

#kc_plan CFSG.KD.SLP.c125346 "c125346.plan.txt" 70920 1888612001174190429
#kc_plan CFSG.KD.SLP.c125346 "c125346.grp.txt" 12122 2233040250350870657
#kc_select CFSG.KD.SLP.c125346 CH CH 510
#kc_select CFSG.KD.SLP.c125346 IXf IX 510
#kc_select CFSG.KD.SLP.c125346 PRf PR 357
#kc_select CFSG.KD.SLP.c125346 GKf GK 510
#kc_listDispatch CFSG.KD.SLP.c125346 WDb wd 104
#kc_listDispatch CFSG.KD.SLP.c125346 Gf G 63

namespace CFSG.KD.SLP.c125346

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 234 286

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 104))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 312 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 234 286 = true := by
  quickRfl

theorem ix : ((List.range 510).all fun k => Nat.blt (IXf k) 510) = true := by quickRfl

theorem plan : planOKP WL CHI 510 IT = true := by quickRfl

end CFSG.KD.SLP.c125346

#kc_each CFSG.KD.SLP.c125346.u 0 63

end
