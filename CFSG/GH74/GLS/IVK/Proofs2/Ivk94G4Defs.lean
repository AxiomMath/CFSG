module

public import CFSG.GH74.GLS.IVK.Statements.Sec9b

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

@[expose] def IVK_9_4_g4_G2three : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Gs : Type) [Group Gs] (z : H) (m : ℕ), 1 ≤ m →
    Gen4 H → CFSG.pRank 2 H ≤ 3 → Hyp94 H Gs z .G2 3 m → LieModel ↥(layer H) .G2 0 3 m

end CFSG.GH74.GLS.IVK
