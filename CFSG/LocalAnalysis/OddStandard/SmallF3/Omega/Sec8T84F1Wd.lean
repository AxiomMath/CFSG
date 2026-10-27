module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8T84Wr (G : Type) [Group G] (t : G) (T1 T2 : Subgroup G) : Prop where
  t_sq : t * t = 1
  comm : ∀ a ∈ T1, ∀ b ∈ T2, a * b = b * a
  inf : T1 ⊓ T2 = ⊥
  swap1 : ∀ a ∈ T1, t * a * t⁻¹ ∈ T2
  swap2 : ∀ a ∈ T2, t * a * t⁻¹ ∈ T1

theorem Sec8T84TData.wr {G : Type} [Group G] [Finite G] {t : G}
    {E T T1 T2 V1 V2 F1 F2 : Subgroup G}
    (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) : Sec8T84Wr G t T1 T2 :=
  ⟨D.t_sq, D.comm, D.inf, D.swap1, D.swap2⟩

end CFSG.OddStandard.SmallF3.Omega
