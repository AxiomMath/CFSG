module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec8T84YData (G : Type) [Group G] [Finite G] (Y O V H : Subgroup G) : Prop where
  O_le : O ≤ Y
  O_norm : (O.subgroupOf Y).Normal
  O_odd : Odd (Nat.card O)
  V_e16 : IsElemAb2 V 4
  V_le : V ≤ Y
  V_norm : (V.subgroupOf Y).Normal
  V_O : ∀ v ∈ V, ∀ o ∈ O, v * o = o * v
  quot : QuotEquivTo Y (V ⊔ O) (alternatingGroup (Fin 6))
  trans : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ y ∈ Y, y * v * y⁻¹ = w
  H_le : H ≤ Y
  H_inf : H ⊓ (V ⊔ O) ≤ O
  H_sup : H ⊔ (V ⊔ O) = Y

end CFSG.OddStandard.SmallF3.Omega
