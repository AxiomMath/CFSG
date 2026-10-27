module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem co1_u42Free :
    SporadicU42Free .Co1 := by
  have hU := u42_fails_card_quotient_center_mem (N := {251596800}) (by simp)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hU hU (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (co1LocalComponentsInput_holds G e t ht B hB).1)
    (outer_comps_of_forall_inner (s := .Co1) (fun β => ?_) _)
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
    CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner β
  exact ⟨g, hg.symm⟩

theorem co2_u42Free :
    SporadicU42Free .Co2 :=
  sporadicU42Free_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) (fun _ _ _ ⟨e⟩ t ht B hB =>
      CFSG.Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B hB)
    (outer_comps_of_forall_inner (s := .Co2) (mem_inner_of_mulEquiv
      CFSG.Sporadic.Co2Cert.co2PermEquiv
      CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner) _)

theorem fi22_u42Free :
    SporadicU42Free .Fi22 := by
  have hUi := u42_fails_card_quotient_center_mem (N := {9196830720}) (by simp)
  have hUo := u42_fails_card_quotient_center_mem (N := {174182400, 1451520}) (by simp)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hUi hUo (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2
        (CFSG.Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
          e t ht B hB)) (fun G _ _ _ hG β hβ2 hβ B hB => ?_)
  rcases CFSG.Sporadic.FischerOddCore.fi22OuterComponentsInput_holds G hG β
      (mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]

theorem fi23_u42Free :
    SporadicU42Free .Fi23 := by
  have hU := u42_fails_card_quotient_center_mem (N := {64561751654400, 9196830720}) (by simp)
  refine sporadicU42Free_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hU hU (fun G _ _ ⟨e⟩ t ht => fi23_inner_comps e t ht)
    (outer_comps_of_forall_inner (s := .Fi23) (fun β => ?_) _)
  change β ∈ inner NativeSporadic.Fi23
  rw [CFSG.Sporadic.FischerOddCore.CTUC_Fi23_all_automorphisms_inner.1]
  trivial

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
