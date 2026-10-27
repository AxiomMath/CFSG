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

#kc_plan CFSG.KD.SLP.c125001 "c125001.plan.txt" 79948 1967216247813662619
#kc_plan CFSG.KD.SLP.c125001 "c125001.grp.txt" 14910 9976390282735883731
#kc_select CFSG.KD.SLP.c125001 CH CH 627
#kc_select CFSG.KD.SLP.c125001 IXf IX 627
#kc_select CFSG.KD.SLP.c125001 PRf PR 423
#kc_select CFSG.KD.SLP.c125001 GKf GK 627
#kc_listDispatch CFSG.KD.SLP.c125001 WDb wd 138
#kc_listDispatch CFSG.KD.SLP.c125001 Gf G 78

namespace CFSG.KD.SLP.c125001

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 76 145

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 138))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 414 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 76 145 = true := by
  quickRfl

theorem ix : ((List.range 627).all fun k => Nat.blt (IXf k) 627) = true := by quickRfl

theorem plan : planOKP WL CHI 627 IT = true := by quickRfl

end CFSG.KD.SLP.c125001

#kc_each CFSG.KD.SLP.c125001.u 0 78

end
