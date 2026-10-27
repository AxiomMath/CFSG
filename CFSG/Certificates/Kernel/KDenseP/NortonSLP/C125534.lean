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

#kc_plan CFSG.KD.SLP.c125534 "c125534.plan.txt" 97085 5637979205400644796
#kc_plan CFSG.KD.SLP.c125534 "c125534.grp.txt" 18276 2637669071674787536
#kc_select CFSG.KD.SLP.c125534 CH CH 765
#kc_select CFSG.KD.SLP.c125534 IXf IX 765
#kc_select CFSG.KD.SLP.c125534 PRf PR 507
#kc_select CFSG.KD.SLP.c125534 GKf GK 765
#kc_listDispatch CFSG.KD.SLP.c125534 WDb wd 174
#kc_listDispatch CFSG.KD.SLP.c125534 Gf G 96

namespace CFSG.KD.SLP.c125534

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 144 231

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 174))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 522 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 144 231 = true := by
  quickRfl

theorem ix : ((List.range 765).all fun k => Nat.blt (IXf k) 765) = true := by quickRfl

theorem plan : planOKP WL CHI 765 IT = true := by quickRfl

end CFSG.KD.SLP.c125534

#kc_each CFSG.KD.SLP.c125534.u 0 96

end
