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

#kc_plan CFSG.KD.SLP.c125506 "c125506.plan.txt" 97476 1977518071263429195
#kc_plan CFSG.KD.SLP.c125506 "c125506.grp.txt" 17572 11023577304069209767
#kc_select CFSG.KD.SLP.c125506 CH CH 729
#kc_select CFSG.KD.SLP.c125506 IXf IX 729
#kc_select CFSG.KD.SLP.c125506 PRf PR 498
#kc_select CFSG.KD.SLP.c125506 GKf GK 729
#kc_listDispatch CFSG.KD.SLP.c125506 WDb wd 156
#kc_listDispatch CFSG.KD.SLP.c125506 Gf G 93

namespace CFSG.KD.SLP.c125506

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 79 157

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 156))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 468 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 79 157 = true := by
  quickRfl

theorem ix : ((List.range 729).all fun k => Nat.blt (IXf k) 729) = true := by quickRfl

theorem plan : planOKP WL CHI 729 IT = true := by quickRfl

end CFSG.KD.SLP.c125506

#kc_each CFSG.KD.SLP.c125506.u 0 93

end
