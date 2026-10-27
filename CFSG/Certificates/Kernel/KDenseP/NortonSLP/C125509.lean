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

#kc_plan CFSG.KD.SLP.c125509 "c125509.plan.txt" 31036 4539304377195912930
#kc_plan CFSG.KD.SLP.c125509 "c125509.grp.txt" 3567 17660928086202174992
#kc_select CFSG.KD.SLP.c125509 CH CH 150
#kc_select CFSG.KD.SLP.c125509 IXf IX 168
#kc_select CFSG.KD.SLP.c125509 PRf PR 129
#kc_select CFSG.KD.SLP.c125509 GKf GK 150
#kc_listDispatch CFSG.KD.SLP.c125509 WDb wd 16
#kc_listDispatch CFSG.KD.SLP.c125509 Gf G 24

namespace CFSG.KD.SLP.c125509

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 292 300

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 16))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 48 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 292 300 = true := by
  quickRfl

theorem ix : ((List.range 168).all fun k => Nat.blt (IXf k) 150) = true := by quickRfl

theorem plan : planOKP WL CHI 168 IT = true := by quickRfl

end CFSG.KD.SLP.c125509

#kc_each CFSG.KD.SLP.c125509.u 0 24

end
