module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

@[expose] def HaradaInput : Prop :=
  (∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S → ∀ E : Subgroup S,
      IsElementaryAbelian 2 E → Nat.card E = 8 → centralizer (E : Set S) = E →
      ∀ P : Subgroup S, ∃ s : Finset S, s.card ≤ 4 ∧ closure (s : Set S) = P) ∧
    ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G), IsElementaryAbelian 2 E →
      Nat.card E = 8 → centralizer (E : Set G) = E →
      ∀ P : Subgroup G, IsPGroup 2 P → ∃ s : Finset G, s.card ≤ 4 ∧ closure (s : Set G) = P

end CFSG.ComponentClassification.HSFLit
