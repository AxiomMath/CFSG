module

public import CFSG.Certificates.Kernel.Orders.He.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held

public section

namespace CFSG.KD.OrdHe

theorem rels_eq : TauCeti.Sporadic.hePresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.hePresentation_transcribed]
  simp [FreeGroup.invRev, rels]

end CFSG.KD.OrdHe

end
