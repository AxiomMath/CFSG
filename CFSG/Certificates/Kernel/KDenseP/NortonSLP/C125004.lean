module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen13.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125004 "c125004.plan.txt" 29766 9203002967866851883
#kc_plan CFSG.KD.SLP.c125004 "c125004.grp.txt" 3885 13802526263863152849
#kc_select CFSG.KD.SLP.c125004 CH CH 168
#kc_select CFSG.KD.SLP.c125004 IXf IX 183
#kc_select CFSG.KD.SLP.c125004 PRf PR 129
#kc_select CFSG.KD.SLP.c125004 GKf GK 168
#kc_listDispatch CFSG.KD.SLP.c125004 WDb wd 28
#kc_listDispatch CFSG.KD.SLP.c125004 Gf G 30

namespace CFSG.KD.SLP.c125004

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 264 278

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 28))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 84 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 264 278 = true := by
  quickRfl

theorem ix : ((List.range 183).all fun k => Nat.blt (IXf k) 168) = true := by quickRfl

theorem plan : planOKP WL CHI 183 IT = true := by quickRfl

end CFSG.KD.SLP.c125004

#kc_each CFSG.KD.SLP.c125004.u 0 30

end
