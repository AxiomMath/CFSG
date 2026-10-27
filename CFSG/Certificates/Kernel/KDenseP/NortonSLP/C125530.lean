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

#kc_plan CFSG.KD.SLP.c125530 "c125530.plan.txt" 33692 2687874246092436477
#kc_plan CFSG.KD.SLP.c125530 "c125530.grp.txt" 4279 4849945000049564765
#kc_select CFSG.KD.SLP.c125530 CH CH 183
#kc_select CFSG.KD.SLP.c125530 IXf IX 192
#kc_select CFSG.KD.SLP.c125530 PRf PR 147
#kc_select CFSG.KD.SLP.c125530 GKf GK 183
#kc_listDispatch CFSG.KD.SLP.c125530 WDb wd 26
#kc_listDispatch CFSG.KD.SLP.c125530 Gf G 30

namespace CFSG.KD.SLP.c125530

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 0 22

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 26))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 78 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 0 22 = true := by
  quickRfl

theorem ix : ((List.range 192).all fun k => Nat.blt (IXf k) 183) = true := by quickRfl

theorem plan : planOKP WL CHI 192 IT = true := by quickRfl

end CFSG.KD.SLP.c125530

#kc_each CFSG.KD.SLP.c125530.u 0 30

end
