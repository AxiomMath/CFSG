module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.SeitzReduction.RankOne

@[expose] def HypothesisOneStar (Y : Type*) [Group Y] : Prop :=
  ∀ x u : MulAut Y, orderOf x = 2 → u ^ 2 = x →
    ∀ E : Subgroup (MulAut Y), E ≤ Subgroup.centralizer {x} → Odd (Nat.card E) →
      (∀ e ∈ E, u * e * u⁻¹ ∈ E) →
      (∀ c : Y, MulAut.conj c * x = x * MulAut.conj c →
        ∀ e ∈ E, MulAut.conj c * e * (MulAut.conj c)⁻¹ ∈ E) →
      ∃ c : Y, MulAut.conj c * x = x * MulAut.conj c ∧
        MulAut.conj c * u * (MulAut.conj c)⁻¹ ∉ E ⊔ Subgroup.zpowers u

end CFSG.SeitzReduction.RankOne
