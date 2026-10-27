module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAltReduce
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieEven
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowLieChar

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowLie

open CFSG Subgroup Assembly.LowTwoRank

theorem lieOther_of_mulEquiv (p : ℕ) (S S' : Type) [Group S] [Group S'] (e : S ≃* S')
    (h : (∃ r : ℕ, r ≠ p ∧ LieChar r S) ∧ ¬ LieChar p S) :
    (∃ r : ℕ, r ≠ p ∧ LieChar r S') ∧ ¬ LieChar p S' := by
  obtain ⟨⟨r, hrp, ⟨τ, n, f, hm⟩⟩, hL⟩ := h
  exact ⟨⟨r, hrp, ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv e hm⟩⟩, fun ⟨τ', n', f', hm'⟩ =>
    hL ⟨τ', n', f', GSThmB.OddQuot.lieModel_of_equiv e.symm hm'⟩⟩

section Certified


theorem rowCore_lieOther :
    RowAlt.RowCore (fun p S => (∃ r : ℕ, r ≠ p ∧ LieChar r S) ∧ ¬ LieChar p S) := by
  intro S _ _ _ hna p hp hp2 hS t ht J hJC hJs htJ hJq L _ _ _ hI ⟨eLJ⟩
  obtain ⟨⟨r, hrp, hr⟩, -⟩ := hS
  by_cases hr2 : r = 2
  · subst hr2
    exact false_of_lieChar_two hr ht hJC hJs hJq
  · obtain ⟨τ', n', f', hadm', hJr⟩ :=
      exists_lieModel_of_lieChar_odd hna hr2 hr ht hJC hJs htJ hJq
    exact false_of_inductionTypeField hp hp2 hI eLJ hr2 hrp hadm' hJr

theorem rowLieOther_holds : RowLieOther :=
  RowAlt.rowFor_of_core lieOther_of_mulEquiv rowCore_lieOther

end Certified

end CFSG.ComponentClassification.HarrisLit.T1.RowLie
