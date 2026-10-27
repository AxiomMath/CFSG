module

public import CFSG.GF2Type.SmithTypeE.E7Order
public import CFSG.LargeExtraspecial.S14C12THyp
public import CFSG.Timmesfeld.Assembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open CFSG.Open CFSG.Blueprint CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

theorem e7_of_outcome
    {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 16) (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (ho : Timmesfeld.Outcome G) :
    ChevalleyExceptionalModel G .E7 2 1 :=
  chevalleyExceptionalModel_E7_of_outcome ho (factorization_card_of_E7 S hw hO)
    (seventeen_dvd_card_of_E7 S hw hO)

theorem e8_of_outcome
    {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 28) (hE : LieModel S.Mbar .E7 0 2 1) (ho : Timmesfeld.Outcome G) :
    ChevalleyExceptionalModel G .E8 2 1 := by
  obtain ⟨h19, h127⟩ := dvd_card_of_E8 S hw hE
  exact chevalleyExceptionalModel_E8_of_outcome ho (factorization_card_of_E8 S hw hE) h19 h127


theorem e7_of_threeFourPlus {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 16) (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hD : ThreeFourPlusClass G {g | IsConj S.z g})
    (hnd : ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4) :
    ChevalleyExceptionalModel G .E7 2 1 := by
  obtain ⟨a, b, ha, hb, h4⟩ := hnd
  exact e7_of_outcome S hw hO
    (Timmesfeld.outcome (hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩))


theorem e8_of_threeFourPlus {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 28) (hE : LieModel S.Mbar .E7 0 2 1)
    (hD : ThreeFourPlusClass G {g | IsConj S.z g})
    (hnd : ∃ a b : G, IsConj S.z a ∧ IsConj S.z b ∧ orderOf (a * b) = 4) :
    ChevalleyExceptionalModel G .E8 2 1 := by
  obtain ⟨a, b, ha, hb, h4⟩ := hnd
  exact e8_of_outcome S hw hE
    (Timmesfeld.outcome (hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩))

end CFSG.GF2Type.SmithTypeE
