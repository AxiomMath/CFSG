module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Lyons
public import CFSG.Certificates.Kernel.Bounds.LyAlt.Rels
import CFSG.Certificates.Kernel.Common.Harness
import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KC.LyA

theorem rels_eq : TauCeti.Sporadic.Lyons.presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.Lyons.presentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem list_bind : eqL list (encList rels) = true := by quickRfl

end CFSG.KC.LyA

end
