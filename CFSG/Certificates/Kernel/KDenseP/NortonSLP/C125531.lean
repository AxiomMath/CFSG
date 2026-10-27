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

#kc_plan CFSG.KD.SLP.c125531 "c125531.plan.txt" 34031 8610055713083275267
#kc_plan CFSG.KD.SLP.c125531 "c125531.grp.txt" 4220 222902689502169455
#kc_select CFSG.KD.SLP.c125531 CH CH 177
#kc_select CFSG.KD.SLP.c125531 IXf IX 186
#kc_select CFSG.KD.SLP.c125531 PRf PR 144
#kc_select CFSG.KD.SLP.c125531 GKf GK 177
#kc_listDispatch CFSG.KD.SLP.c125531 WDb wd 24
#kc_listDispatch CFSG.KD.SLP.c125531 Gf G 36

namespace CFSG.KD.SLP.c125531

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 22 34

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 24))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 72 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 22 34 = true := by
  quickRfl

theorem ix : ((List.range 186).all fun k => Nat.blt (IXf k) 177) = true := by quickRfl

theorem plan : planOKP WL CHI 186 IT = true := by quickRfl

end CFSG.KD.SLP.c125531

#kc_each CFSG.KD.SLP.c125531.u 0 36

end
