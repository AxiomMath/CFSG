module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Four

public section

namespace CFSG.KD.FamJ4

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)],
    [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)],
    [(2, true), (2, true)],
    [(2, false), (0, false), (2, true), (0, true)],
    [(2, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (2, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true)],
    [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]]

theorem rels_eq : TauCeti.Sporadic.j4Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.j4Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

end CFSG.KD.FamJ4

end
