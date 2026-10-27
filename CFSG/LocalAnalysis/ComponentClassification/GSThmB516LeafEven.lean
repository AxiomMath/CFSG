module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36EvenOddCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem cf516EvenRow :
    CF516EvenRow := by
  intro S _ _ he _ _ _ σ P _ p f _ _ _ _ t _ ht2 J _ hJ _ _ _ _ _ _ _
  obtain ⟨τ, n, f', hadm, hm⟩ := he
  have hO := HarrisLit.N36.EvenOddCore.evenLieInvolutionOddCoreFact_holds S τ n f' hm t ht2
  exact CatLeaf.involutionCentralizersComponentFree_of_evenLieType ⟨τ, n, f', hadm, hm⟩ t ht2 _
    (B5a.isComponent_of_isPComponent hO hJ)

end CFSG.ComponentClassification.GSThmB
