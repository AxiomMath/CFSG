module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerSplit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

theorem rankThreeUC_of_inputs (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Open.IsKProper G)
    (hchar : CFSG.Open.IsCharTwoType G) (he : CFSG.Open.evenRank G = 3)
    (hpre : CFSG.Open.rankThreeAschCoreLocal G 2) (hD1 : TheoremD1 G) (hD2 : TheoremD2 G)
    (hsigI : SignalizerCentralNonConstrained G) (hsigII : SignalizerNoncentralPart G)
    (hcon : TransitivityComponentCase G) (h13 : GL83InvariantTwoSylow G)
    (hrel : GL83RelativePairExclusion G) (hlayer : GL83GenericLayer G)
    (h349 : GL83GenericUniquePlane G) (hstr : GL83GenericStructure G)
    (h627 : GL83SmallRankPrimeThree G) (h632 : GL83SmallRankStructure G)
    (h633 : GL83SmallRankQ8 G) (hplane : GL83SmallRankUniquePlane G) :
    CFSG.Open.rankThreeUC G := by
  have hS : Setting G := ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩
  have hU0 := fullCoreLocal_of_cases hS hD1 (signalizerCase_of_parts hS hsigI hsigII)
    (transitivityCase_of_containment hS hD1 (transitivityReduction_of_componentCase hS hcon) h13
      (gl83InvariantTwoContainment_of_relativePairExclusion hS hD1
        (transitivityReduction_of_componentCase hS hcon) h13 hrel))
  exact rankThreeUC_of_steps hS hD2 hU0 (nonStrongEmbeddingCase_of_cases hS hD2 hU0
    (genericCase_of_inputs hS hD1 hD2 hU0 hlayer h349 hstr)
    (smallRankCase_of_inputs hS hD2 hU0 h627 h632 h633 hplane))

end CFSG.LocalAnalysis.RankThreeTheoremC
