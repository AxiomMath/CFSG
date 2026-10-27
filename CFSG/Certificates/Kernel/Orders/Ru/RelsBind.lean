module

public import CFSG.Certificates.Kernel.Orders.Ru.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

namespace CFSG.KD.OrdRu

theorem rels_eq : TauCeti.Sporadic.ruPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.ruPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

end CFSG.KD.OrdRu

end
