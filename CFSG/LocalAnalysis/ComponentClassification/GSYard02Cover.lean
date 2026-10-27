module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Cases

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup Blueprint

@[expose] def CoverHyp (Q : Type) [Group Q] [Finite Q] : Prop :=
  IsQuasisimple Q ∧ center Q ≠ ⊥ ∧ IsPGroup 2 (center Q) ∧ IsCyclic (center Q) ∧
    3 ≤ CFSG.pRank 2 Q ∧ GH74.Gen4 Q

@[expose] def CoverLow : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → Open.twoRank (Q ⧸ center Q) ≤ 2 → False

@[expose] def CoverGH : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CoverHyp Q → GH74.GH74Conclusion (Q ⧸ center Q) →
    SylowFourJoined Q

theorem coverCase_of_low_gh
    (hL : CoverLow) (hG : CoverGH) : CoverCase := by
  intro Q _ _ hQ hz h2 hcyc hr hgen hcat
  have hhyp : CoverHyp Q := ⟨hQ, hz, h2, hcyc, hr, hgen⟩
  by_cases hlow : Open.twoRank (Q ⧸ center Q) ≤ 2
  · exact (hL Q hhyp hlow).elim
  · exact hG Q hhyp (GH74.Filter.filter _ hcat hQ.2.2 (by omega) (GH74.Gen4.quotient _ hgen))

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
