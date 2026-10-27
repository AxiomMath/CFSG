module

public import CFSG.Certificates.Kernel.Orders.Co1.Rels
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.One

public section

namespace CFSG.KD.OrdCo1

theorem rels_eq : TauCeti.Sporadic.co1Presentation.relatorLetters = rels := by
  rw [TauCeti.Sporadic.co1Presentation_relatorLetters]
  decide +kernel

end CFSG.KD.OrdCo1

end
