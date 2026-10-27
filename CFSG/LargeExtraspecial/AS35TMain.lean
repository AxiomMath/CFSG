module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35TPSym
public import CFSG.LargeExtraspecial.AS35TFSeven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions

namespace S14

theorem asc512PbarStmt : Asc512PbarStmt := fun _ _ _ S hS _ ht htM =>
  ⟨Setting.AS35T.rho_t_mem_pbar S htM, Setting.AS35T.isExtraspecialPGroup_pbar hS ht,
    Setting.AS35T.card_pbar hS ht,
    fun _ hx hc => Setting.AS35T.eq_one_or_of_commute_pbar hS ht htM hx hc,
    fun _ hc hct _ hx => Setting.AS35T.conj_mem_pbar_of_commute hS ht htM hc hct hx,
    fun _ hx _ hv => Setting.AS35T.pbar_fix_commSpace hS ht htM hx hv,
    fun _ hx _ hv => Setting.AS35T.pbar_sub_mem_commSpace hS ht htM hx hv⟩

theorem asc512FiveFiveStmt :
    ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp →
      ∀ t ∈ S.DSet, ∀ x ∈ S.M, (∀ q ∈ S.QG, x * (t * q * t⁻¹ * q⁻¹) = (t * q * t⁻¹ * q⁻¹) * x) →
        x * t = t * x := fun _ _ _ S hS _ ht _ hxM hx =>
  Setting.AS35T.fiveFive S hS ht hxM hx

theorem asc512FiveEightStmt : Asc512FiveEightStmt := fun _ _ _ _ hS _ ht htM X hXM hXt hXP hOE =>
  Setting.AS35T.fiveEight hS ht htM X hXM hXt hXP hOE

theorem asc512FiveTwelveSevenStmt : Asc512FiveTwelveSevenStmt := fun _ _ _ _ hS _ ht htM =>
  Setting.AS35T.fiveTwelveSeven hS ht htM

theorem asc512SymStmt : Asc512SymStmt := fun _ _ _ S hS _ ht htM W hW hWfix hWc =>
  Setting.AS35T.exists_pbar_sub_of_fixSpace S hS ht htM W hW hWfix hWc

end S14

end CFSG.LargeExtraspecial
