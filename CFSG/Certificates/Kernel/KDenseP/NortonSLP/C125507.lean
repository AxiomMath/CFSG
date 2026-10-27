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

#kc_plan CFSG.KD.SLP.c125507 "c125507.plan.txt" 97392 14823466753632487675
#kc_plan CFSG.KD.SLP.c125507 "c125507.grp.txt" 18459 11604931045480020969
#kc_select CFSG.KD.SLP.c125507 CH CH 768
#kc_select CFSG.KD.SLP.c125507 IXf IX 768
#kc_select CFSG.KD.SLP.c125507 PRf PR 516
#kc_select CFSG.KD.SLP.c125507 GKf GK 768
#kc_listDispatch CFSG.KD.SLP.c125507 WDb wd 170
#kc_listDispatch CFSG.KD.SLP.c125507 Gf G 99

namespace CFSG.KD.SLP.c125507

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 157 242

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 170))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 510 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 157 242 = true := by
  quickRfl

theorem ix : ((List.range 768).all fun k => Nat.blt (IXf k) 768) = true := by quickRfl

theorem plan : planOKP WL CHI 768 IT = true := by quickRfl

end CFSG.KD.SLP.c125507

#kc_each CFSG.KD.SLP.c125507.u 0 99

end
