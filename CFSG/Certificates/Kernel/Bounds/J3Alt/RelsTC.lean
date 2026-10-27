module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Three
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Rels
import CFSG.Certificates.Kernel.Common.Harness
import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KC.J3A

theorem rels_eq : TauCeti.Sporadic.j3Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.j3Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem list_bind : eqL list (encList rels) = true := by quickRfl

end CFSG.KC.J3A

end
