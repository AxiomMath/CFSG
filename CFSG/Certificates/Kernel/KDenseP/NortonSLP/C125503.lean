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

#kc_plan CFSG.KD.SLP.c125503 "c125503.plan.txt" 36364 9564944353630581986
#kc_plan CFSG.KD.SLP.c125503 "c125503.grp.txt" 4713 7947891618616744242
#kc_select CFSG.KD.SLP.c125503 CH CH 201
#kc_select CFSG.KD.SLP.c125503 IXf IX 213
#kc_select CFSG.KD.SLP.c125503 PRf PR 156
#kc_select CFSG.KD.SLP.c125503 GKf GK 201
#kc_listDispatch CFSG.KD.SLP.c125503 WDb wd 32
#kc_listDispatch CFSG.KD.SLP.c125503 Gf G 36

namespace CFSG.KD.SLP.c125503

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP

@[expose] noncomputable def E :
    List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  prodPairs CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 0 22

@[expose] noncomputable def WD (σ : Nat) : List Nat := WDb (Nat.mod σ (nat_lit 32))

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen := decW (WD σ)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.SLP.Gen11.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (CFSG.KD.SLP.Gen11.chk WL) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

theorem weq : wordsEqB WD (CFSG.KC.KDense.Y443.words (E ++ E ++ E ++ [])) 96 = true := by quickRfl

theorem idx : idxOK CFSG.AGLEmbedding.Norton.Gen11.gen11Gens CFSG.KD.SLP.Gen11.S 0 22 = true := by
  quickRfl

theorem ix : ((List.range 213).all fun k => Nat.blt (IXf k) 201) = true := by quickRfl

theorem plan : planOKP WL CHI 213 IT = true := by quickRfl

end CFSG.KD.SLP.c125503

#kc_each CFSG.KD.SLP.c125503.u 0 36

end
