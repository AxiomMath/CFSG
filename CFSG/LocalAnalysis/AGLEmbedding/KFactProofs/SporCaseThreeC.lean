module

public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData

public section

namespace CFSG.AGLEmbedding

theorem sporCaseThreePrimeData_of_tc_cp {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (htc : TCGenDatum X p) (hcp : CoverPointDatum X p) :
    SporCaseThreePrimeData X p :=
  Or.inr (Or.inr ⟨fun T => Or.inl (weakCoreOfTC X p htc T),
    Or.inr (coverWeakGen_of_coverPointDatum hp2 hcp)⟩)

end CFSG.AGLEmbedding
