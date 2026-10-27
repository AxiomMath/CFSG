module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

theorem cfL2InvPair : GSThmB.CFL2InvPair :=
  fun _ _ _ _ _ _ hp2 _ hY t ht => l2InvPair_conclusion hp2 hY t ht

end CFSG.ComponentClassification.AutL2Facts
