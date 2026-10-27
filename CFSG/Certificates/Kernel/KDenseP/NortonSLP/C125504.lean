module

public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Run
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen11Prog
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Data
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.SLP.c125504 "c125504.plan.txt" 32352 4896709306795705255
#kc_plan CFSG.KD.SLP.c125504 "c125504.grp.txt" 3983 11162862059683973061
#kc_select CFSG.KD.SLP.c125504 CH CH 168
#kc_select CFSG.KD.SLP.c125504 IXf IX 174
#kc_select CFSG.KD.SLP.c125504 PRf PR 138
#kc_select CFSG.KD.SLP.c125504 GKf GK 168
#kc_listDispatch CFSG.KD.SLP.c125504 WDb wd 22
#kc_listDispatch CFSG.KD.SLP.c125504 Gf G 33

namespace CFSG.KD.SLP.c125504

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 22 33

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 22))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 66 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 22 33 = true := by
  quickRfl

theorem ix : ((List.range 174).all fun k => Nat.blt (IXf k) 168) = true := by quickRfl

theorem plan : planOKP WL CHI 174 IT = true := by quickRfl

end CFSG.KD.SLP.c125504

#kc_each CFSG.KD.SLP.c125504.u 0 33

end
