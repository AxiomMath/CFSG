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

#kc_plan CFSG.KD.SLP.c125341 "c125341.plan.txt" 27406 1368089640072109620
#kc_plan CFSG.KD.SLP.c125341 "c125341.grp.txt" 3230 12059748898159357012
#kc_select CFSG.KD.SLP.c125341 CH CH 141
#kc_select CFSG.KD.SLP.c125341 IXf IX 147
#kc_select CFSG.KD.SLP.c125341 PRf PR 114
#kc_select CFSG.KD.SLP.c125341 GKf GK 141
#kc_listDispatch CFSG.KD.SLP.c125341 WDb wd 20
#kc_listDispatch CFSG.KD.SLP.c125341 Gf G 24

namespace CFSG.KD.SLP.c125341

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 21 31

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 20))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 60 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 21 31 = true := by
  quickRfl

theorem ix : ((List.range 147).all fun k => Nat.blt (IXf k) 141) = true := by quickRfl

theorem plan : planOKP WL CHI 147 IT = true := by quickRfl

end CFSG.KD.SLP.c125341

#kc_each CFSG.KD.SLP.c125341.u 0 24

end
