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

#kc_plan CFSG.KD.SLP.c125005 "c125005.plan.txt" 27445 1251513908809662592
#kc_plan CFSG.KD.SLP.c125005 "c125005.grp.txt" 3390 5882719405908481313
#kc_select CFSG.KD.SLP.c125005 CH CH 147
#kc_select CFSG.KD.SLP.c125005 IXf IX 156
#kc_select CFSG.KD.SLP.c125005 PRf PR 120
#kc_select CFSG.KD.SLP.c125005 GKf GK 147
#kc_listDispatch CFSG.KD.SLP.c125005 WDb wd 20
#kc_listDispatch CFSG.KD.SLP.c125005 Gf G 24

namespace CFSG.KD.SLP.c125005

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 278 288

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 20))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 60 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen13.gen13Gens CFSG.KD.SLP.Gen13.S 278 288 = true := by
  quickRfl

theorem ix : ((List.range 156).all fun k => Nat.blt (IXf k) 147) = true := by quickRfl

theorem plan : planOKP WL CHI 156 IT = true := by quickRfl

end CFSG.KD.SLP.c125005

#kc_each CFSG.KD.SLP.c125005.u 0 24

end
