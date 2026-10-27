module

public import CFSG.GF2Type.SmithTypeE.Parts
public import CFSG.Yardstones.M3aba7dc4b8a8.Definitions
public import CFSG.LargeExtraspecial.BridgeSetting

public section

namespace CFSG.GF2Type.SmithTypeE

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial.Bridge CFSG.Yardstones.M3aba7dc4b8a8
open scoped MatrixGroups

theorem widthTenE6Case_of_parts (hA : PartA) (hB : PartB) : WidthTenE6Case := by
  intro G _ _ _ z hset hext hcard Mbar _ hMbar
  have hz : orderOf z = 2 := hset.2.2.2.2.1
  have hcard' : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * 10) := by rw [hcard]
  refine ⟨fun hL => hB G hset.1 z hz hext hcard' Mbar hMbar ?_,
    fun hU => hA G hset.1 z hz hext hcard' Mbar hMbar ?_⟩
  · rw [generalizedFitting_eq_timmesfeldFStar]; exact hL
  · rw [generalizedFitting_eq_timmesfeldFStar]; exact hU

theorem widthsSixteenTwentyEightCase_of_parts (hC : PartC) (hD : PartD) :
    WidthsSixteenTwentyEightCase := by
  intro G _ _ _ z hset hext w hcard Mbar _ hMbar hsimp t ht htext
  have hz : orderOf z = 2 := hset.2.2.2.2.1
  rw [← generalizedFitting_eq_timmesfeldFStar] at htext
  rw [timmesfeldIsExtraspecial_iff] at htext
  refine ⟨fun h16 hc hqu => ?_, fun h28 hc hqu => ?_⟩
  · subst h16
    rw [← generalizedFitting_eq_timmesfeldFStar] at hc hqu
    exact hC G hset.1 z hz hext hcard Mbar hMbar hsimp ⟨t, ht, htext, hc, hqu⟩
  · subst h28
    rw [← generalizedFitting_eq_timmesfeldFStar] at hc hqu
    exact hD G hset.1 z hz hext hcard Mbar hMbar hsimp ⟨t, ht, htext, hc, hqu⟩

end CFSG.GF2Type.SmithTypeE
