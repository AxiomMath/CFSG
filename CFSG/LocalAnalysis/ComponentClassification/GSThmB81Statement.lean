module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Lemma81StatementK : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H),
    (SectionRank.IsKGroupCat H ∨ IsSimpleGroup H) → h.Sec8Case → 8 ≤ Nat.card h.P →
    Nonempty (generalizedFitting H ≃* alternatingGroup (Fin 10)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        (Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) ∨
          (p = 3 ∧ f = 1 ∧ Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 6)))) ∧
        (Blueprint.LieModel (generalizedFitting H) .PSL 4 p f ∨
          Blueprint.LieModel (generalizedFitting H) .PSU 4 p f)

end CFSG.ComponentClassification.GSThmB
