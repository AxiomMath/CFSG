module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8T84GSet (G : Type) [Group G] [Finite G] (t : G)
    (E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G) : Prop where
  E8 : IsElemAb2 E 8
  XO : Sec8XO G t E Y1 Y2
  T_syl : IsSylow2Of T (normalizer (E : Set G))
  D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2
  T1_eq : T1 = T ⊓ Y1
  T2_eq : T2 = T ⊓ Y2
  V1_eq : V1 = E ⊓ Y1
  V2_eq : V2 = E ⊓ Y2

@[expose] def sec8t84g_Q {G : Type} [Group G] (E E0 : Subgroup G) : Subgroup G :=
  normalizer (E : Set G) ⊓ normalizer (E0 : Set G)

end CFSG.OddStandard.SmallF3.Omega
