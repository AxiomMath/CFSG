module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddStandard.ONan76

structure AlperinFrame {G : Type*} [Group G] (n : ℕ) (v₁ v₂ v₃ s t : G) : Prop where
  comm₁₂ : v₁ * v₂ = v₂ * v₁
  comm₁₃ : v₁ * v₃ = v₃ * v₁
  comm₂₃ : v₂ * v₃ = v₃ * v₂
  pow₁ : v₁ ^ 2 ^ n = 1
  pow₂ : v₂ ^ 2 ^ n = 1
  pow₃ : v₃ ^ 2 ^ n = 1
  card_V : Nat.card (Subgroup.closure ({v₁, v₂, v₃} : Set G)) = 2 ^ (3 * n)
  s_v₁ : s⁻¹ * v₁ * s = v₂
  s_v₂ : s⁻¹ * v₂ * s = v₃
  s_v₃ : s⁻¹ * v₃ * s = v₁ * v₂⁻¹ * v₃
  t_v₁ : t⁻¹ * v₁ * t = v₃⁻¹
  t_v₂ : t⁻¹ * v₂ * t = v₂⁻¹
  t_v₃ : t⁻¹ * v₃ * t = v₁⁻¹
  t_sq : t * t = 1
  t_s : t⁻¹ * s * t = s⁻¹
  s_four : s ^ 4 = 1 ∨ s ^ 4 = v₁ * v₃

end CFSG.OddStandard.ONan76
