module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStab

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

theorem cfAutL2Stab : GSThmB.CFAutL2Stab :=
  fun _ _ _ _ _ hp hp2 hf hY t ht => autL2Stab_conclusions hp hp2 hf hY t ht

end CFSG.ComponentClassification.AutL2Facts
