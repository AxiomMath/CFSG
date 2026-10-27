module

public import CFSG.GF2Type.Aschbacher1977WidthAtMostTwo
public import CFSG.RankThree.GF2n.Statements
import CFSG.GF2Type.ListIntro
public import CFSG.LargeExtraspecial.BridgeNat

public section

namespace CFSG.GF2Type

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.RankThree.GF2n
  CFSG.LargeExtraspecial.Bridge
open scoped MatrixGroups

section Cases

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
  {z : G} (hz : orderOf z = 2)
  (hext : IsExtraspecialPGroup 2
    (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)))) {w : ℕ}
  (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
    2 ^ (1 + 2 * w))

include hnonab hz hext hcard

theorem gf2TypeList_of_width_two (h77 : Aschbacher1977WidthAtMostTwoStatement) (hw : w = 2) :
    GF2TypeList G := by
  rcases (h77 G hnonab z hz hext w hcard).2 hw with h | h | h | h | h | h | h | h | h
  · exact gf2TypeList_of_psu (by norm_num) h
  · exact gf2TypeList_of_three (s := .PSL) (n := 4) (by simp) h
  · exact gf2TypeList_of_three (s := .PSU) (n := 4) (by simp) h
  · exact gf2TypeList_of_three (s := .G2) (n := 0) (by simp) h
  · exact gf2TypeList_of_alternating (k := 8) (by simp) h
  · exact gf2TypeList_of_alternating (k := 9) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .M12) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .J2) (by simp) h
  · exact gf2TypeList_of_sporadic (s := .J3) (by simp) h

end Cases

end CFSG.GF2Type
