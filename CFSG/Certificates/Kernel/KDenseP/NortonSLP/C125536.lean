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

#kc_plan CFSG.KD.SLP.c125536 "c125536.plan.txt" 63188 5431160355668324069
#kc_plan CFSG.KD.SLP.c125536 "c125536.grp.txt" 10100 4733696710718507618
#kc_select CFSG.KD.SLP.c125536 CH CH 423
#kc_select CFSG.KD.SLP.c125536 IXf IX 423
#kc_select CFSG.KD.SLP.c125536 PRf PR 306
#kc_select CFSG.KD.SLP.c125536 GKf GK 423
#kc_listDispatch CFSG.KD.SLP.c125536 WDb wd 80
#kc_listDispatch CFSG.KD.SLP.c125536 Gf G 60

namespace CFSG.KD.SLP.c125536

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 296 336

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 80))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.GenD13.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.GenD13.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 240 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.GenD13.genD13Gens CFSG.KD.SLP.GenD13.S 296 336 = true := by
  quickRfl

theorem ix : ((List.range 423).all fun k => Nat.blt (IXf k) 423) = true := by quickRfl

theorem plan : planOKP WL CHI 423 IT = true := by quickRfl

end CFSG.KD.SLP.c125536

#kc_each CFSG.KD.SLP.c125536.u 0 60

end
