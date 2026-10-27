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

#kc_plan CFSG.KD.SLP.c125344 "c125344.plan.txt" 78942 15892121908880718280
#kc_plan CFSG.KD.SLP.c125344 "c125344.grp.txt" 14992 1026609849161709290
#kc_select CFSG.KD.SLP.c125344 CH CH 630
#kc_select CFSG.KD.SLP.c125344 IXf IX 630
#kc_select CFSG.KD.SLP.c125344 PRf PR 426
#kc_select CFSG.KD.SLP.c125344 GKf GK 630
#kc_listDispatch CFSG.KD.SLP.c125344 WDb wd 138
#kc_listDispatch CFSG.KD.SLP.c125344 Gf G 78

namespace CFSG.KD.SLP.c125344

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 105 174

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 138))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 414 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 105 174 = true := by
  quickRfl

theorem ix : ((List.range 630).all fun k => Nat.blt (IXf k) 630) = true := by quickRfl

theorem plan : planOKP WL CHI 630 IT = true := by quickRfl

end CFSG.KD.SLP.c125344

#kc_each CFSG.KD.SLP.c125344.u 0 78

end
