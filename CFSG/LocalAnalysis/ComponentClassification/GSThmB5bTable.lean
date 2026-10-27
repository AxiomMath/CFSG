module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Local
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem table (hB1 : ConjFixStatement) (hCF : CFProp23Fusion) : h.Table54 := by
  by_contra hT
  obtain ⟨g, hgW, heS, heP, he⟩ := hCF H h hT
  exact (hB1 H h g hgW heS heP).2 he

end Hyp52

end CFSG.ComponentClassification.GSThmB
