module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Ambient

variable {M : Type*} [Group M]

@[expose] def F3S (G : Subgroup M) (u : M) (p : ℕ) : Prop :=
  ∀ x ∈ G, orderOf x = p → u * x * u⁻¹ = x⁻¹ →
    ¬ IsPGroup p ↥(Subgroup.closure {w : M | ∃ c ∈ Subgroup.closure
      {y : M | y ∈ G ∧ u * y = y * u ∧ Odd (orderOf y)}, w = c * x * c⁻¹})

end Ambient

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
