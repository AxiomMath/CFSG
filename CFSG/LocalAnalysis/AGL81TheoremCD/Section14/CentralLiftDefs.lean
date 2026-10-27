module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

variable {G : Type*} [Group G]

@[expose] def FixesKleinFour (θ : MulAut G) : Prop :=
  ∃ a b : G, θ a = a ∧ θ b = b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b

@[expose] def FixesTorusPrime (Q : ℕ) (θ : MulAut G) : Prop :=
  ∃ y : G, θ y = y ∧ ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ ¬ r ∣ Q ^ 3 * (Q ^ 2 - 1) ∧ orderOf y = r

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
