module

public import CFSG.LargeExtraspecial.AS35YTDims
public import CFSG.LargeExtraspecial.AS35YSWMain
public import CFSG.LargeExtraspecial.A2ModMain
public import CFSG.LargeExtraspecial.AS35YSMain
public import CFSG.LargeExtraspecial.AS35YSSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem fixW_eq_bot_YT
    (hPSL : S12PSLModuleInputN) (hSp : S12SpModuleInputN) (hO : S12OmegaModuleInputN)
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hfam : S14.Asc512PSLFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      S14.Asc512PSpFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      S14.Asc512POmegaFam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc ∨
      S14.Asc512U33Fam (S.LbarAsc ⧸ center S.LbarAsc) S.EhatAsc)
    (h : RadSing_YS S) : fixW_YS S = ⊥ := by
  have h5127 := S14.asc512FiveTwelveSevenStmt
  rcases hfam with ⟨hnd, m, hm, hL⟩ | ⟨hnd, m, hm, hL⟩ | ⟨hnd, m, hm, hL⟩ | hU
  ·
    by_cases hm4 : 4 ≤ m
    · obtain ⟨rfl, h6⟩ := psl_dim_YT hPSL hS hst h5127 hnd hm4 hL h
      have hX := AS35YS.card_O_eq_two_mul_of_psl4 (q0_YS_nondegenerate h) hL h6
        (card_dvd_card_O_YS hS hst hnd h)
      exact fixW_eq_bot_of_omega_YS hS hst hnd h (card_O_eq_YS hS hst hnd h hX) (Or.inl h6)
    · obtain rfl : m = 3 := by omega
      exact (false_of_psl3_YS hS hst hnd hL).elim
  ·
    obtain ⟨hL3, h8⟩ := psp_dim_YT hSp hS hst h5127 ⟨hnd, m, hm, hL⟩ h
    exact fixW_eq_bot_of_spin_YS hS hst hnd h hL3 h8
  ·
    have hdim := pomega_dim_YT hO hS hst h5127 hnd hm hL h
    have hX := AS35YS.card_O_eq_two_mul_of_omega (q0_YS_nondegenerate h) hL hdim
      (card_dvd_card_O_YS hS hst hnd h)
    exact fixW_eq_bot_of_omega_YS hS hst hnd h (card_O_eq_YS hS hst hnd h hX) (Or.inr (by omega))
  ·
    exact (false_of_u33_YS S14.asc512U33ModuleInput hS hst h5127 hU h).elim

end Setting

namespace S14

theorem asc512FixFreeStmt_of_radSingN'
    (hPSL : S12PSLModuleInputN) (hSp : S12SpModuleInputN) (hO : S12OmegaModuleInputN)
    (hRad : Asc512FixRadSingStmt) : Asc512FixFreeStmt := by
  intro G _ _ S hS hst hfam v hv
  have h := Setting.radSing_YS hRad asc512U33FixNonsingStmt_proof hS hst hfam
  have hbot := Setting.fixW_eq_bot_YT hPSL hSp hO hS hst hfam h
  have hvW : v ∈ Setting.fixW_YS S := hv
  rw [hbot, Submodule.mem_bot] at hvW
  exact hvW

section Certified


theorem asc512FixFreeStmt_of_radSingN
    (hRad : Asc512FixRadSingStmt) : Asc512FixFreeStmt :=
  asc512FixFreeStmt_of_radSingN' s12PSLModuleInputN s12SpModuleInputN s12OmegaModuleInputN hRad

end Certified

end S14

end CFSG.LargeExtraspecial
