module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.HaradaNorton
public import CFSG.Certificates.Kernel.Bounds.HNAlt.Rels
import CFSG.Certificates.Kernel.Common.Harness
import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.KC.HNA

theorem rels_eq : TauCeti.Sporadic.hnPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.hnPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

theorem list_bind : eqL list (encList rels) = true := by quickRfl

end CFSG.KC.HNA

end
