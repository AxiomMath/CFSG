module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveTData
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M7.c716201

open CFSG.KC.KDenseP.MonSeven

@[expose] noncomputable def P : Prs :=
  tri CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive.m5tEqs []

end CFSG.KD.M7.c716201

#kc_plan CFSG.KD.M7.c716201 "c716201.plan.txt" 8029 18054742125364148823
#kc_plan CFSG.KD.M7.c716201 "c716201.grp.txt" 4327 3815203080914139044
#kc_select CFSG.KD.M7.c716201 CH CH 183
#kc_select CFSG.KD.M7.c716201 IXf IX 183
#kc_select CFSG.KD.M7.c716201 PRf PR 165
#kc_select CFSG.KD.M7.c716201 GKf GK 183
#kc_listDispatch CFSG.KD.M7.c716201 Gf G 21

namespace CFSG.KD.M7.c716201

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M7L.grpRP P CH PRf Gf g

end CFSG.KD.M7.c716201

#kc_each CFSG.KD.M7.c716201.u 0 21

end
