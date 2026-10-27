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

#kc_plan CFSG.KD.SLP.c125513 "c125513.plan.txt" 7221 10235875612321711958
#kc_plan CFSG.KD.SLP.c125513 "c125513.grp.txt" 2005 9604038330290648935
#kc_select CFSG.KD.SLP.c125513 CH CH 99
#kc_select CFSG.KD.SLP.c125513 IXf IX 99
#kc_select CFSG.KD.SLP.c125513 PRf PR 69
#kc_select CFSG.KD.SLP.c125513 GKf GK 99
#kc_listDispatch CFSG.KD.SLP.c125513 WDb wd 22
#kc_listDispatch CFSG.KD.SLP.c125513 Gf G 11

namespace CFSG.KD.SLP.c125513

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  targetPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S
    CFSG.AGLEmbedding.Norton.Gen11.gen11Targets

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 22))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 66 = true := by quickRfl

theorem tgt : tgtOK CFSG.KD.SLP.Gen11.S 342 CFSG.AGLEmbedding.Norton.Gen11.gen11Targets = true := by
  quickRfl

theorem ix : ((List.range 99).all fun k => Nat.blt (IXf k) 99) = true := by quickRfl

theorem plan : planOKP WL CHI 99 IT = true := by quickRfl

end CFSG.KD.SLP.c125513

#kc_each CFSG.KD.SLP.c125513.u 0 11

end
