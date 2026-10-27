module

public import CFSG.Quasithin.H13.U3L15
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15L
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative commutatorElement

theorem stmt13_3_15_of_F4
    (h1332 : Stmt13_3_2_F4) (h13314 : A6.Stmt13_3_14_F4)
    (hhatP : U3HatL2Plus_F4) : A6.Stmt13_3_15_F4 := by
  intro G _ _ T L V V₂ X I₂ hH hV hzv hV2 hA5 hXhat hXn hI₂
  obtain ⟨-, -, ⟨-, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, -, hcomm, hmod⟩ := hVall V hV
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, hnat, -⟩ | ⟨hu, -, -⟩
  · exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
    exact hA5.false e
  · obtain ⟨S⟩ := setting4_of_case_b_F4 h1332 hH hV hzv h6
    exact u3Stmt13_3_15_of_A6_F4 h1332 h13314 hhatP S hV2 hXhat hXn hI₂
  · exfalso
    rw [hzv, card_bot] at hc2
    norm_num at hc2
  · have hnh : ¬ IsHatA6 L := by
      obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hl
      have hsSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
        HSType.isSimpleGroup_SL_three_two
      have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e).2 hsSL
      have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
        have hna0 : ∃ a b : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), a * b ≠ b * a := by
          decide
        obtain ⟨a, b, hab⟩ := hna0
        exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
      exact not_isHatA6_of_center_eq_bot (center_eq_bot_of_isSimpleGroup hna)
    exact u3Stmt13_3_15_of_L32_F4 h1332 h13314 hH hl hnat hV hzv hV2 (hXn hnh) hI₂
  · exact u3Stmt13_3_15_of_U3_F4 h1332 h13314 hH hu hV hV2 (hXn (not_isHatA6_of_U3 hu)) hI₂

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

end CFSG.Quasithin.H13.U3
