module

public import CFSG.GF2Type.Entry
public import CFSG.LargeExtraspecial.AS35WSect

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.LargeExtraspecial CFSG.LargeExtraspecial.Bridge CFSG.GH74

theorem exists_setting_of_extraspecial {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)))) {w : ℕ}
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * w)) :
    ∃ S : Setting G, S.z = z ∧ S.width = w := by
  obtain ⟨h1, h2⟩ := timmesfeld_hypotheses hext hcard
  exact ⟨Setting.ofFStar z hz h1, rfl, width_ofFStar hz h1 h2⟩

theorem sectionalTwoRankLE_four_of_width_two {G : Type} [Group G] [Finite G] (S : Setting G)
    (hw : S.width = 2) : SectionalTwoRankLE G 4 := by
  obtain ⟨P, -, hPM⟩ := S.exists_sylow_le_M
  exact AS35W.fourGen_of_sylow P fun Q hQ =>
    AS35W.fourGen_of_le_subgroup (S.gen4_M hw) (hQ.trans hPM) (P.isPGroup'.to_le hQ)

end CFSG.GF2Type.Aschbacher1977
