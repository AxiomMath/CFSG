module

public import CFSG.Certificates.Kernel.Orders.Co2.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Two

public section

namespace CFSG.KD.OrdCo2

theorem rels_eq : TauCeti.Sporadic.co2Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.co2Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

end CFSG.KD.OrdCo2

end
