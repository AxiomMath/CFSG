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

#kc_plan CFSG.KD.SLP.c125343 "c125343.plan.txt" 68263 16166991111132237134
#kc_plan CFSG.KD.SLP.c125343 "c125343.grp.txt" 11608 15111239807232837144
#kc_select CFSG.KD.SLP.c125343 CH CH 486
#kc_select CFSG.KD.SLP.c125343 IXf IX 486
#kc_select CFSG.KD.SLP.c125343 PRf PR 345
#kc_select CFSG.KD.SLP.c125343 GKf GK 486
#kc_listDispatch CFSG.KD.SLP.c125343 WDb wd 96
#kc_listDispatch CFSG.KD.SLP.c125343 Gf G 64

namespace CFSG.KD.SLP.c125343

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 57 105

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 96))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 288 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 57 105 = true := by
  quickRfl

theorem ix : ((List.range 486).all fun k => Nat.blt (IXf k) 486) = true := by quickRfl

theorem plan : planOKP WL CHI 486 IT = true := by quickRfl

end CFSG.KD.SLP.c125343

#kc_each CFSG.KD.SLP.c125343.u 0 64

end
