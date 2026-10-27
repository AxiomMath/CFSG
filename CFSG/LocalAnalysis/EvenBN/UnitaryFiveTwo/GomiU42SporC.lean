module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Spor
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicSmall
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutJanko
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.Walter.J1Props.Elt

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem j2_u42Free :
    SporadicU42Free .J2 :=
  sporadicU42Free_of_card (s := .J2) (N := 604800) CFSG.Sporadic.J2.card_J2 (by norm_num)

theorem j3_u42Free :
    SporadicU42Free .J3 := by
  intro D _ _ _ hs α S h
  obtain ⟨e⟩ := hs
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, hcard, -⟩ := autModel_exists_row CFSG.Sporadic.SmallOddCore.j3_autModel
    CFSG.Sporadic.SmallOddCore.j3Rows (fun r => CFSG.Sporadic.SmallOddCore.tp 6156 r.rep)
    CFSG.Sporadic.SmallOddCore.ClassRow.centOrder CFSG.Sporadic.SmallOddCore.ClassRow.outer
    hcover (fun r hr => ⟨(hrows r hr).2.2.1, (hrows r hr).2.2.2.2.1⟩)
    (e.trans CFSG.Sporadic.Schreier.j3PermEquiv) α h.1
  have hmem := List.mem_map_of_mem (f := fun r : CFSG.Sporadic.SmallOddCore.ClassRow =>
    (r.outer, r.classSize, r.centOrder)) hr
  rw [hmap] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  have hdvd := h.card_dvd_eqLocus
  rw [hcard] at hdvd
  rcases hmem with ⟨-, -, hc⟩ | ⟨-, -, hc⟩ <;> rw [hc] at hdvd <;> norm_num at hdvd

theorem suz_u42Free :
    SporadicU42Free .Suz := by
  intro D _ _ hD hs α S h
  obtain ⟨e⟩ := hs
  by_cases hα : α ∈ inner D
  · exact h.false_of_inner_comps hD hα (isoInvariant_card_quotient_center {20160})
      (u42_fails_card_quotient_center_mem (N := {20160}) (by norm_num))
      (fun t ht B hB =>
        CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order
          e t ht B hB)
  · have hdvd := h.card_dvd_eqLocus
    rcases suz_outer_card e α h.1 hα with hcard | hcard <;> rw [hcard] at hdvd <;>
      norm_num at hdvd

theorem on_u42Free :
    SporadicU42Free .ONan := by
  intro D _ _ hD hs α S h
  by_cases hα : α ∈ inner D
  · exact h.false_of_inner_comps hD hα (isoInvariant_card_quotient_center {20160})
      (u42_fails_card_quotient_center_mem (N := {20160}) (by norm_num)) (fun t ht B hB =>
        Set.mem_singleton_iff.2
          (CFSG.Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
            hs t ht B hB))
  · obtain ⟨e⟩ := hs
    have hα2 : α * α = 1 := mul_self_eq_one_of_orderOf_eq_two h.1
    have hS : S ≤ CFSG.Sporadic.Schreier.fixSub α := by
      rw [← eqLocus_eq_fixSub α]
      exact h.2.1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨s, hs2⟩ : ∃ s : S, orderOf s = 2 :=
      exists_prime_orderOf_dvd_card' 2 (by rw [h.2.2.2.2.2]; norm_num)
    have hsf : (s : D) ∈ CFSG.Sporadic.Schreier.fixSub α := hS s.2
    have hz : orderOf (⟨(s : D), hsf⟩ : CFSG.Sporadic.Schreier.fixSub α) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hs2]
    obtain ⟨hJ⟩ := CFSG.ComponentClassification.SolMax.ONOut.nonempty_jankoHyp₀
      (CFSG.ComponentClassification.SolMax.ONOut.onOuterLocalInput_holds D ⟨e⟩ α hα2 hα) hz
    obtain ⟨e'⟩ := hJ.nonempty_mulEquiv_walterJ1
    have hcard : Nat.card (CFSG.Sporadic.Schreier.fixSub α) = 175560 :=
      (Nat.card_congr e'.toEquiv).trans CFSG.Walter.J1Props.card_walterJ1
    have hdvd := h.card_dvd_eqLocus
    rw [eqLocus_eq_fixSub, hcard] at hdvd
    norm_num at hdvd

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
