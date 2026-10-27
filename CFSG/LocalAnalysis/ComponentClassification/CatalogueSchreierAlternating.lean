module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingOutsideSix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix

public section

namespace CFSG.ComponentClassification.CatalogueSchreierAlternating

open OuterAutomorphisms

theorem alternating_schreier (n : ℕ) (hn : 5 ≤ n) :
    Group.IsSolvable (Outer (alternatingGroup (Fin n))) := by
  by_cases hsix : n = 6
  · subst n
    exact DegreeSix.outer_solvable
  · exact outer_solvable_outside_six (by omega)

theorem alternating_schreier_of_equiv {G : Type*} [Group G] (n : ℕ) (hn : 5 ≤ n)
    (equivalence : G ≃* alternatingGroup (Fin n)) : Group.IsSolvable (Outer G) := by
  let := alternating_schreier n hn
  exact OuterAutomorphisms.solvable_of_equiv equivalence.symm

theorem alternating_schreier_of_nonempty_equiv {G : Type*} [Group G] (n : ℕ) (hn : 5 ≤ n)
    (hequivalence : Nonempty (G ≃* alternatingGroup (Fin n))) :
    Group.IsSolvable (Outer G) := by
  obtain ⟨equivalence⟩ := hequivalence
  exact alternating_schreier_of_equiv n hn equivalence

end CFSG.ComponentClassification.CatalogueSchreierAlternating
