module

public import CFSG.Certificates.Kernel.Orders.McL.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.McLaughlin

public section

namespace CFSG.KD.OrdMcL

theorem rels_eq : TauCeti.Sporadic.mclPresentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.mclPresentation_transcribed]
  simp [FreeGroup.invRev, rels]

end CFSG.KD.OrdMcL

end
