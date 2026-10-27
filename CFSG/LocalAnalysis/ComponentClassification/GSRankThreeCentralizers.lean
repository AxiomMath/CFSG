module

public import CFSG.GH74.NoComponent
public import CFSG.GH74.GLS.C3.Layer1.St1RigGen

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

section RankCertificates

theorem three_le_pRank_of_not_catalog {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hnotCat : ¬ CFSG.Blueprint.Catalog X) : 3 ≤ CFSG.pRank 2 X := by
  by_contra h
  have h2 := CFSG.GH74.GLS.C3.Layer1.PumpRigid.two_le_pRank_of_isSimple (inferInstance) hnonab
  have hr : CFSG.Open.twoRank X = 2 := by
    rw [← CFSG.GH74.GLS.pRank_two_eq_twoRank]
    omega
  exact hnotCat (CFSG.GH74.catalog_of_ghList
    (CFSG.GH74.ghList_of_twoRank_eq_two hnonab hr))

theorem three_le_pRank_centralizer_of_not_catalog {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hnotCat : ¬ CFSG.Blueprint.Catalog X) (x : X) (hx : orderOf x = 2) :
    3 ≤ CFSG.pRank 2 ↥(Subgroup.centralizer ({x} : Set X)) :=
  CFSG.GH74.GLS.TwoThin.rankThreeCentralizers X inferInstance hnonab
    (three_le_pRank_of_not_catalog hnonab hnotCat) x hx

end RankCertificates

end CFSG.ComponentClassification.GSThmB

end
