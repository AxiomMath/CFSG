module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteFourgroupInner : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ W : Subgroup (MulAut S), (∀ w ∈ W, w * w = 1) → Nat.card W = 4 →
      ∃ w ∈ W, w ≠ 1 ∧ w ∈ (MulAut.conj : S →* MulAut S).range

end CFSG.ComponentClassification.FooteLit
