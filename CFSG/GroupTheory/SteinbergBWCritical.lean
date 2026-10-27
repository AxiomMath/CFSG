module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.CriticalDefinition

public section

namespace CFSG.GroupTheory.PG

open CFSG.SectionRank.Ccomm

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

theorem exists_thompsonCritical (hP : IsPGroup p P) :
    (∃ C : Subgroup P, ThompsonCritical C) ∧
      (Nontrivial P → ∀ C : Subgroup P, ThompsonCritical C → C ≠ ⊥) :=
  ⟨(thompson_critical_subgroup hP).1, fun hnt C hC => (thompson_critical_subgroup hP).2 C hC hnt⟩

end CFSG.GroupTheory.PG
