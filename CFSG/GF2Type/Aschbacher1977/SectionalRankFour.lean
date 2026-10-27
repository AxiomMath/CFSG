module

public import CFSG.GF2Type.Aschbacher1977.RankThree
public import CFSG.LargeExtraspecial.AS35WMain
public import CFSG.Milestones.CL_LIT_GH74_sectional_two_rank_four
public import CFSG.GF2Type.Aschbacher1977.Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.LargeExtraspecial


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem gh74Models_of_width_two
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * 2)) :
    AS35W.GH74List G := by
  obtain ⟨S, -, hw⟩ := exists_setting_of_extraspecial hz hext hcard
  exact CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab
    (three_le_twoRank_of_width_two hnonab S hw) (sectionalTwoRankLE_four_of_width_two S hw)

end CFSG.GF2Type.Aschbacher1977
