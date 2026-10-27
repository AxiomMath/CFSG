module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G]

@[expose] def normOf (r x : G) : G := x * (r * x * r⁻¹) * (r ^ 2 * x * (r ^ 2)⁻¹)

structure NormSetting (P E U : Subgroup G) (r : G) : Prop where
  U_le_E : U ≤ E
  E_le_P : E ≤ P
  E_sq : ∀ e ∈ E, e ^ 2 = 1
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  PP : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ U
  r_cube : r ^ 3 = 1
  r_P : ∀ p ∈ P, r * p * r⁻¹ ∈ P
  r_U : ∀ u ∈ U, r * u * r⁻¹ ∈ U
  r_E : ∀ e ∈ E, r * e * r⁻¹ * e⁻¹ ∈ U
  r_fpf : ∀ p ∈ P, r * p * r⁻¹ * p⁻¹ ∈ U → p ∈ E

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
