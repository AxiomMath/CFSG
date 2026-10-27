module

public import CFSG.CGT.M24S.Defs

public section

namespace CFSG.CGT.M24S

variable {G : Type} [Group G]

@[expose] def CentreTransvecting (T : Subgroup G) (t w : G) : Prop :=
  ∀ s ∈ T, w * s * w⁻¹ * s⁻¹ = 1 ∨ w * s * w⁻¹ * s⁻¹ = t

@[expose] def HasComplement (T H : Subgroup G) : Prop :=
  ∃ L : Subgroup G, L ≤ H ∧ T ⊓ L = ⊥ ∧ T ⊔ L = H

@[expose] def SqDerivedEq (P : Subgroup G) (t : G) : Prop :=
  (∀ y ∈ ⁅P, P⁆, y ^ 2 = 1 ∨ y ^ 2 = t) ∧ ∃ y ∈ ⁅P, P⁆, y ^ 2 = t

end CFSG.CGT.M24S
