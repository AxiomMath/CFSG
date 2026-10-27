module

public import CFSG.Certificates.Kernel.Orders.Fi22.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyTwo

public section

namespace CFSG.KD.OrdFi22

theorem rels_eq : TauCeti.Sporadic.fi22Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.fi22Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

end CFSG.KD.OrdFi22

end
