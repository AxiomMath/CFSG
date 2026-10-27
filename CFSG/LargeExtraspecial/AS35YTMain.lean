module

public import CFSG.LargeExtraspecial.AS35YTCaseB
public import CFSG.LargeExtraspecial.AS35YTFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace S14

@[expose] def Asc512FixOddStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    InspNondeg _ S.EhatAsc → ∀ m : ℕ,
    (m = 3 ∧ LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSL 4 2 1 ∨
      4 ≤ m ∧ LieModel (S.LbarAsc ⧸ center S.LbarAsc) .PSp m 2 1 ∨
      m = 4 ∧ (LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus 4 2 1 ∨
        LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus 4 2 1)) →
    finrank (ZMod 2) (Setting.commU_YS S) = 2 * m + 1 →
    ∀ r ∈ Setting.fixW_YS S, r ∈ Setting.commU_YS S → S.q r = 1 →
      (∀ v ∈ Setting.fixW_YS S, v ∈ Setting.commU_YS S → v = 0 ∨ v = r) → False

section Certified

theorem asc512FixRadSingStmt_of_odd (hOdd : Asc512FixOddStmt) : Asc512FixRadSingStmt := by
  intro G _ _ S hS hst hnd ⟨m, hm, hL⟩ v hvW hvperp
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  by_contra hqv
  have hq1 : S.q v = 1 := (h01 _).resolve_left hqv
  have hvW' : v ∈ Setting.fixW_YS S := hvW
  have hvU : v ∈ Setting.commU_YS S := Setting.mem_commU_YS.mpr fun w hw => hvperp w hw
  rcases hL with hL | hL | hL | hL
  · rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | h5
    · obtain ⟨hdim, hR⟩ := Setting.odd_of_psl4_YT hS hst hnd hL hvW' hvU hqv
      exact hOdd G S hS hst hnd 3 (Or.inl ⟨rfl, hL⟩) hdim v hvW' hvU hq1 hR
    · exact hqv (Setting.radSing_of_psl_YT hS hst hnd h5 hL v hvW' fun w hw => hvperp w hw)
  · obtain ⟨hdim, hR⟩ := Setting.odd_of_psp_YT hS hst hnd hm hL hvW' hvU hqv
    exact hOdd G S hS hst hnd m (Or.inr (Or.inl ⟨hm, hL⟩)) hdim v hvW' hvU hq1 hR
  · rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | h5
    · obtain ⟨hdim, hR⟩ := Setting.odd_of_pomega4_YT hS hst hnd (Or.inl hL) hvW' hvU hqv
      exact hOdd G S hS hst hnd 4 (Or.inr (Or.inr ⟨rfl, Or.inl hL⟩)) hdim v hvW' hvU hq1 hR
    · exact hqv (Setting.radSing_of_pomega_YT hS hst hnd h5 (Or.inl hL) v hvW'
        fun w hw => hvperp w hw)
  · rcases (show m = 4 ∨ 5 ≤ m by omega) with rfl | h5
    · obtain ⟨hdim, hR⟩ := Setting.odd_of_pomega4_YT hS hst hnd (Or.inr hL) hvW' hvU hqv
      exact hOdd G S hS hst hnd 4 (Or.inr (Or.inr ⟨rfl, Or.inr hL⟩)) hdim v hvW' hvU hq1 hR
    · exact hqv (Setting.radSing_of_pomega_YT hS hst hnd h5 (Or.inr hL) v hvW'
        fun w hw => hvperp w hw)

theorem asc512FixFreeStmt_of_odd
    (hOdd : Asc512FixOddStmt) : Asc512FixFreeStmt :=
  asc512FixFreeStmt_of_radSingN (asc512FixRadSingStmt_of_odd hOdd)

end Certified

end S14

end CFSG.LargeExtraspecial
