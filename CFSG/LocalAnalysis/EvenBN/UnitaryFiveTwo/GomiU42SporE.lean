module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven) in
theorem fi24prime_u42Free :
    SporadicU42Free .Fi24Prime := by
  have hUi := u42_fails_card_quotient_center_mem (N := {64561751654400}) (by simp)
  have hUo := u42_fails_card_quotient_center_mem (N := {4089470473293004800, 9196830720})
    (by simp)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hUi hUo (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2
        (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
          e t ht B hB).1) (fun G _ _ _ hG β hβ2 hβ B hB => ?_)
  rcases CFSG.Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds G hG β
      (mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]

theorem hn_u42Free :
    SporadicU42Free .HN := by
  have hUi := u42_fails_card_quotient_center_mem (N := {44352000}) (by simp)
  have hUo := u42_fails_card_quotient_center_mem (N := {1814400}) (by simp)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hUi hUo (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (hnLocalComponentsInput_holds G e t ht B hB))
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => ?_)
  obtain ⟨eS⟩ := CFSG.Sporadic.HNOddCore.hn_outer_involution_fixSub e β hβ2 hβ
  exact CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) eS compsSatisfy_perm_ten

theorem ly_u42Free :
    SporadicU42Free .Ly := by
  have hU := u42_fails_card_quotient_center_mem (N := {19958400}) (by simp)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hU hU (fun G _ _ hG t ht => ?_)
    (outer_comps_of_forall_inner (s := .Ly) (fun β => ?_) _)
  · obtain ⟨hq, -, ⟨eA⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
    have hcard : Nat.card (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) =
        19958400 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    exact compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400}) hcard
  · change β ∈ inner NativeSporadic.Ly
    rw [lyOuterTrivialInput]
    trivial

theorem th_u42Free :
    SporadicU42Free .Th :=
  sporadicU42Free_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun G _ _ hG t ht => compsSatisfy_of_charP
      ((CFSG.Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G
        hG).1 t ht).1 _)
    (outer_comps_of_forall_inner (s := .Th) (fun β => by
      have h : inner (NativeSporadic.Carrier .Th) = ⊤ := CFSG.Sporadic.ThSchreier.inner_Th
      rw [h]
      trivial) _)

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
