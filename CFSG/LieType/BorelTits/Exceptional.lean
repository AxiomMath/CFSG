module

public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.LieType.BorelTits.Classical
public import CFSG.LieType.BorelTits.TitsClause
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.BorelTits

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

theorem holds_adjointQuotient (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : Holds (AdjointQuotient τ K) p :=
  Holds.center_quotient (holds_adjointGroup_tag τ K p)

theorem holds_of_untwistedChevalleyModel {G : Type} [Group G] {τ : Tag} {p f : ℕ} [Fact p.Prime]
    (h : UntwistedChevalleyModel G τ (p ^ f)) : Holds G p := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have := charP_of_natCard_eq (K := K) hK
  exact (holds_adjointQuotient τ K p).of_mulEquiv e.symm

theorem holds_of_chevalleyExceptionalModel_untwisted {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {p f : ℕ} (h : ChevalleyExceptionalModel G t p f) (ht : t ≠ .twistedE6) (ht' : t ≠ .trialityD4) :
    Holds G p := by
  obtain ⟨hadm, hmodel⟩ := h
  have : Fact p.Prime := ⟨hadm.1⟩
  cases t
  all_goals first
    | exact holds_of_untwistedChevalleyModel hmodel
    | exact absurd rfl ht
    | exact absurd rfl ht'
    | exact hmodel.elim

end CFSG.LieType.BorelTits
