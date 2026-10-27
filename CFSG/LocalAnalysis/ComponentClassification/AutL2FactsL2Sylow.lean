module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem cfL2Sylow : GSThmB.CFL2Sylow := by
  intro Y _ _ p f _ hp2 _ hY T hT
  exact l2Sylow_conclusions hp2 hY T hT

end CFSG.ComponentClassification.AutL2Facts
