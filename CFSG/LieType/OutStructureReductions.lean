module

public import CFSG.LieType.OutStructureAssembly
public import CFSG.LieType.OutStructureI713
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section7.SevenOneFourSplitOfI713

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem sylow_normal_outer_of_pRank_le_one :
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      CFSG.Open.IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 →
        CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
          ∀ S : Sylow p (Outer K), (S : Subgroup (Outer K)).Normal :=
  sylow_normal_outer_of_pRank_le_one_of_I_7_13_2_5 i_7_13_2_5_holds

end CFSG.LieType.OutStructure

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem sevenOneFourSplit :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourSplit :=
  sevenOneFourSplit_of_I_7_13_2_5 CFSG.LieType.OutStructure.i_7_13_2_5_holds

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
