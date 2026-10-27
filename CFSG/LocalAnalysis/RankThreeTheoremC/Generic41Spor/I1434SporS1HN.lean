module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434SporS1Base
public import CFSG.RankThree.PartOne.KS.HNFiveCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Blueprint CFSG.RankThree.PartOne.KS.HNFive CFSG.Sporadic.GLQ.HNTwoRank

theorem hn_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup NativeSporadic.HN := by
  have hR : Rel (fun j => (⟨Rg (iQ j), Rg_mem _⟩ : J)) ⟨Rg iZ, Rg_mem _⟩ ⟨Rg iX, Rg_mem _⟩
      (fun j => ⟨Rg (iR j), Rg_mem _⟩) Mm XU cx BU cr := by
    apply Rel.of_injective J.subtype J.subtype_injective
    simp only [Subgroup.coe_subtype]
    exact hnFive_rel
  exact @HasNonabelianFiveSubgroup.of_mulEquiv J NativeSporadic.HN inferInstance inferInstance
    hnEquivJ.symm (SporS1.hasNonabelianFiveSubgroup_of_commData hR.commData hR.z_eq)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
