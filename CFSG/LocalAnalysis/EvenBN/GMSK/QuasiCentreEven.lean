module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreDatum
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEvenBenderOuter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CatEvenBender

section Certified


theorem qFixedRootDatum_center_eq_bot_of_PSL3 {D : Type} [Group D] [Finite D] {n : ℕ}
    (hD : LieModel D .PSL 3 2 (2 * n)) {α : MulAut D}
    (hα : orderOf α = 2) (hout : α ∉ (MulAut.conj : D →* MulAut D).range)
    {J : Subgroup D} (d : QFixedRootDatum D n α J) : center J = ⊥ := by
  set F := α.toMonoidHom.eqLocus (MonoidHom.id D) with hF
  have hDp : IsPComponent 2 (J.subgroupOf F) :=
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent d.isComponent
  have hDm : LieModel (J.subgroupOf F ⧸ center (J.subgroupOf F)) .PSU 3 2 n :=
    lieModel_quotient_center_of_mulEquiv (Subgroup.subgroupOfEquivOfLe d.le_fixed).symm d.model
  rcases SeitzReduction.UnitaryPilot.psl_outer_fixed_even (LieModel.admissible hD) hD α hα hout
    with h | ⟨he, h⟩ | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · exfalso
    obtain ⟨hadm', hmD, -⟩ := h _ hDp
    exact absurd ((evenTagDet_U3 n).tag_eq_of_simple d.isComponent.1
      (SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSL hmD) hDm hadm' hmD) (by decide)
  · obtain ⟨-, hmD⟩ := h _ hDp
    have hs : IsSimpleGroup (J.subgroupOf F) :=
      SeitzReduction.LinearPilot.isSimpleGroup_of_lieModel_PSU hmD
    exact center_eq_bot_of_mulEquiv_aux (Subgroup.subgroupOfEquivOfLe d.le_fixed)
      (SeitzReduction.F4Pilot.center_eq_bot_of_isQuasisimple d.isComponent.1 hs)
  · exact ((evenTagDet_U3 n).false_of_isComponent_statedSp (Or.inl rfl)
      (fun _ _ h => two_pow_six_dvd_card_of_lieModel_PSU3 h) hk hr Φ d.isComponent hDm).elim
  · exact (h _ hDp).elim

theorem qFixedRootSelector_evenLieType : QFixedRootSelector fun D _ => EvenLieType D := by
  intro D _ _ hDs heven n α J d
  have hnab := d.nonabelian_ambient
  haveI := hDs
  have hout : α ∉ (MulAut.conj : D →* MulAut D).range := fun hin =>
    SeitzReduction.F4Pilot.false_of_isComponent_fixedSubgroup_inner hnab
      (ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType heven)
      d.orderOf_eq hin d.isComponent
  have hDm : LieModel (J.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)) ⧸
      center (J.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)))) .PSU 3 2 n :=
    lieModel_quotient_center_of_mulEquiv (Subgroup.subgroupOfEquivOfLe d.le_fixed).symm d.model
  have hD : LieModel D .PSL 3 2 (2 * n) :=
    catSU3EvenOuterList n D hDs hnab heven α d.orderOf_eq hout _ d.isComponent hDm
  exact qFixedRootDatum_center_eq_bot_of_PSL3 hD d.orderOf_eq hout d

end Certified

end CFSG.LocalAnalysis.EvenBN.GMSK
