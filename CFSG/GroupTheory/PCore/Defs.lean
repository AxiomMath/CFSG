module

public import Mathlib.GroupTheory.PGroup
public import CFSG.GroupTheory.PCore.Construction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import Mathlib.Data.Rat.Floor

public section

namespace CFSG

open scoped Pointwise

variable (p : ℕ) (G : Type*) [Group G]

@[expose]
def oddCore : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}

instance oddCore_normal : (oddCore G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

end CFSG
