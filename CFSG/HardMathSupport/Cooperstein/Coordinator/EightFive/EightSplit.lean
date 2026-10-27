module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V]

theorem le_stabSub_top (L : Subgroup (MulAut V)) : L ≤ stabSub (⊤ : Subgroup V) :=
  fun _ _ _ => by simp only [Subgroup.mem_top]

variable [Finite V]

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
