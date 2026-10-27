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

#kc_plan CFSG.KD.SLP.c125538 "c125538.plan.txt" 32261 2124105825310643017
#kc_plan CFSG.KD.SLP.c125538 "c125538.grp.txt" 3984 1018593853564648715
#kc_select CFSG.KD.SLP.c125538 CH CH 168
#kc_select CFSG.KD.SLP.c125538 IXf IX 183
#kc_select CFSG.KD.SLP.c125538 PRf PR 138
#kc_select CFSG.KD.SLP.c125538 GKf GK 168
#kc_listDispatch CFSG.KD.SLP.c125538 WDb wd 22
#kc_listDispatch CFSG.KD.SLP.c125538 Gf G 30

namespace CFSG.KD.SLP.c125538

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 343 354

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 22))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 66 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 343 354 = true := by
  quickRfl

theorem ix : ((List.range 183).all fun k => Nat.blt (IXf k) 168) = true := by quickRfl

theorem plan : planOKP WL CHI 183 IT = true := by quickRfl

end CFSG.KD.SLP.c125538

#kc_each CFSG.KD.SLP.c125538.u 0 30

end
