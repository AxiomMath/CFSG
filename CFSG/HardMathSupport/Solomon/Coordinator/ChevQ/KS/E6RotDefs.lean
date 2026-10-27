module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

structure RotData (S : Type*) [Group S] where
  g₁ : S
  g₂ : S
  t : S
  g_comm : g₁ * g₂ = g₂ * g₁
  g_indep : ∀ i j : ℤ, g₁ ^ i * g₂ ^ j ∈ Subgroup.center S → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j
  t_sq : t ^ 2 = 1
  t_not_central : t ∉ Subgroup.center S
  t_comm : t * (g₁ * g₂ ^ 2) = (g₁ * g₂ ^ 2) * t
  center_card : Nat.card (Subgroup.center S) ≤ 3

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
