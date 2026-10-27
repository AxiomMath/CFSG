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

#kc_plan CFSG.KD.SLP.c125340 "c125340.plan.txt" 28816 506396642430902464
#kc_plan CFSG.KD.SLP.c125340 "c125340.grp.txt" 3934 12412966077341062144
#kc_select CFSG.KD.SLP.c125340 CH CH 177
#kc_select CFSG.KD.SLP.c125340 IXf IX 177
#kc_select CFSG.KD.SLP.c125340 PRf PR 132
#kc_select CFSG.KD.SLP.c125340 GKf GK 177
#kc_listDispatch CFSG.KD.SLP.c125340 WDb wd 32
#kc_listDispatch CFSG.KD.SLP.c125340 Gf G 25

namespace CFSG.KD.SLP.c125340

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 0 21

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 32))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen7.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen7.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 96 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.MON5_7.Gen7.gen7Gens CFSG.KD.SLP.Gen7.S 0 21 = true := by
  quickRfl

theorem ix : ((List.range 177).all fun k => Nat.blt (IXf k) 177) = true := by quickRfl

theorem plan : planOKP WL CHI 177 IT = true := by quickRfl

end CFSG.KD.SLP.c125340

#kc_each CFSG.KD.SLP.c125340.u 0 25

end
