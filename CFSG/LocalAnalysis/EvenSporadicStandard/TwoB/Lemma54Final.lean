module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Residual54
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54NormMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Layer54SchreierMain
public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.SemisimpleComponentStructure

variable {G : Type} [Group G] [Finite G] {t z : G}

theorem outer_component_solvable_of_schreier
    (hSch : SchreierFor CFSG.Blueprint.Catalog)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hCtop : centZ z ≠ ⊤) (i : ComponentIndex ↥(centZ z)) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥i.val) := by
  have hKc : CFSG.IsComponent i.val := (CFSG.isComponent_iff_open i.val).2 i.property
  obtain ⟨hperf, hsimple, hnab⟩ := hKc.1
  have hQtop : i.val.map (centZ z).subtype ≠ ⊤ := by
    intro h
    exact hCtop (top_unique (h ▸ map_subtype_le _))
  let e : ↥i.val ≃* ↥(i.val.map (centZ z).subtype) :=
    Subgroup.equivMapOfInjective i.val (centZ z).subtype (centZ z).subtype_injective
  have hout : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥i.val ⧸ center ↥i.val)) := by
    refine outer_solvable_of_kProper_image hSch hK hQtop hnab
      ((QuotientGroup.mk' (center ↥i.val)).comp e.symm.toMonoidHom) ?_
    exact (QuotientGroup.mk'_surjective _).comp e.symm.surjective
  have : Group.IsPerfect ↥i.val := hperf
  have := hout
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥i.val

section Certified


theorem ds81Lemma54Core_of_schreier (hSch : SchreierFor CFSG.Blueprint.Catalog) :
    DS81Lemma54Core := by
  intro G _ _ L t z hS hc hCt hP
  obtain ⟨d⟩ := hS.exists_level55 hc hCt
  have hz2 : orderOf z = 2 := (Subgroup.orderOf_mk z hc.hz).symm.trans hc.loc.order_z
  have hodd : CFSG.Open.standardComponentOddCore ↥(centZ z) = ⊥ := by
    simpa using hS.std.oddCore z hz2
  have := hS.std.simple
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hCtop : centZ z ≠ ⊤ := centralizer_ne_top_of_simple hS.std.nonabelian hz1
  exact d.centPair_le_layer_of_normalizes hodd hP
    (outer_component_solvable_of_schreier hSch hS.std.kProper hCtop)
    (fun i _ hk _ hn => d.conj_mem_component hodd hP i hk hn)

end Certified

section Lemma54


theorem ds81Lemma54_of_schreier (hSch : SchreierFor CFSG.Blueprint.Catalog)
    (hI : HypothesisOne (Carrier .B)) (h25 : Finkelstein77.Asc76Lemma25)
    (h210 : DS81Lemma210Two) : DS81Lemma54 :=
  ds81Lemma54_of_core hI h25 h210 (ds81Lemma54Core_of_schreier hSch)

end Lemma54

end CFSG.EvenSporadicStandard.TwoB
