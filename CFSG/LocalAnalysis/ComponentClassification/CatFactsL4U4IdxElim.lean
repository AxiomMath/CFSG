module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxL34

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Idx

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer

@[expose] def IndexElimOuter : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp52 H),
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel (OddBar h.J) .PSL 2 p (2 * f) ∧
        conjugate h.K h.a = h.K ∧ (Blueprint.LieModel (ZStarBar h.K) .PSL 4 p f ∨
          Blueprint.LieModel (ZStarBar h.K) .PSU 4 p f ∨
          ∃ e : ℕ, f = 2 * e ∧ Blueprint.LieModel (ZStarBar h.K) .POmegaMinus 4 p e)) →
      h.a ∉ h.K ⊔ coreActionKernel h.K → h.T ≤ zpowers h.a ⊔ h.B

theorem indexElim_of_case3
    (h3 : IndexElimOuter) : CFProp23IndexElim := by
  intro H _ _ h hcase
  rcases hcase with ⟨n, hn, hJ, hKa, hK⟩ | ⟨hJ, hKa, -, hK⟩ | ⟨hrow, hout⟩
  · exact T_le_case_alt h hn hJ hKa hK
  · exact T_le_case_l34 h hJ hKa hK
  · exact h3 H h hrow hout

end Idx

end CFSG.ComponentClassification.CatFactsL4U4
