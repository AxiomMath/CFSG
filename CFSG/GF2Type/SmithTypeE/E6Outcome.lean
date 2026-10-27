module

public import CFSG.GF2Type.SmithTypeE.E6Order
public import CFSG.GF2Type.SmithTypeE.L9Cent
public import CFSG.LargeExtraspecial.S14C12THyp
public import CFSG.Timmesfeld.Assembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open scoped MatrixGroups

theorem e6_of_outcome
    {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 10) (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    (ho : Timmesfeld.Outcome G) :
    ChevalleyExceptionalModel G .E6 2 1 := by
  rcases outcome_PSL9_or_PSp12_or_E6 ho (factorization_card_of_L6 S hw hL)
      (thirtyOne_dvd_card_of_L6 S hL) with hA | hSp | hE
  · exact absurd (dvd_card_centralizer_PSL9_127 hA (exists_sylow_le_M S))
      (not_dvd_card_M_of_L6_127 S hw hL)
  · exact absurd (Sp12.seventeen_dvd_card_centralizer_PSp12 hSp (exists_sylow_le_M S))
      (not_seventeen_dvd_card_M_of_L6 S hw hL)
  · exact Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (by decide) hE

theorem e6_of_threeFourPlus {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hL : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)))
    (hD : ThreeFourPlusClass G {g | IsConj S.z g})
    (hnd : ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4) :
    ChevalleyExceptionalModel G .E6 2 1 := by
  obtain ⟨a, b, ha, hb, h4⟩ := hnd
  exact e6_of_outcome S hw hL
    (Timmesfeld.outcome (hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩))

end CFSG.GF2Type.SmithTypeE
