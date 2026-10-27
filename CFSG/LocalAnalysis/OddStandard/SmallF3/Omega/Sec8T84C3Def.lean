module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

structure WreathMod {Γ : Type} [Group Γ] (H P M1 M2 : Subgroup Γ) (u : Γ) : Prop where
  p_le1 : P ≤ M1
  p_le2 : P ≤ M2
  le1 : M1 ≤ H
  le2 : M2 ≤ H
  comm : ∀ a ∈ M1, ∀ b ∈ M2, a * b * a⁻¹ * b⁻¹ ∈ P
  inf : M1 ⊓ M2 ≤ P
  sup : M1 ⊔ M2 ⊔ zpowers u = H
  u_not : u ∉ M1 ⊔ M2
  swap1 : ∀ a ∈ M1, u * a * u⁻¹ ∈ M2
  swap2 : ∀ a ∈ M2, u * a * u⁻¹ ∈ M1
  quot1 : QuotEquivTo M1 P (alternatingGroup (Fin 6))
  quot2 : QuotEquivTo M2 P (alternatingGroup (Fin 6))

end C10

end CFSG.OddStandard.SmallF3.Omega
