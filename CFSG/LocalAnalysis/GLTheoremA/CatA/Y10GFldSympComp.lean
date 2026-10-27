module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympComp

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  isPerfect_commutator_sympFour commutatorEquivAlternating)
open CFSG.RankThree.PartOne.KCSpComm

variable {m : ℕ} {K : Type} [Field K]

theorem nonempty_fixSubgroup_fieldAut_equiv [NeZero m] {p : ℕ} (hp : Odd p) {σ : K ≃+* K}
    (hσ : σ ^ p = 1) :
    Nonempty (↥(fixSubgroup (fieldAut m K σ)) ≃* StatedProj (StatedSp m (descentField σ))) := by
  have hfix : fixSubgroup (fieldAut m K σ) = (subfieldInj (r := m) σ).range := by
    rw [range_subfieldInj (r := m) σ, ← spFixedGroup_fieldAut_eq_range (r := m) hp hσ]
    exact Subgroup.ext fun x => mem_fixSubgroup.trans mem_spFixedGroup.symm
  exact ⟨(MulEquiv.subgroupCongr hfix).trans
    (MonoidHom.ofInjective (subfieldInj_injective (r := m) σ)).symm⟩

variable [Finite K]

theorem nonempty_quotCenter_equiv_of_glaPComponent_fieldAut (hm : 2 ≤ m) {p : ℕ} (hp : Odd p)
    {σ : K ≃+* K} (hσ : σ ^ p = 1) (hne : ¬(m = 2 ∧ Nat.card (descentField σ) = 2))
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent p (fixSubgroup (fieldAut m K σ)) J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp m (descentField σ))) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨e⟩ := nonempty_fixSubgroup_fieldAut_equiv (m := m) hp hσ
  obtain ⟨hs, hperf⟩ := simple_perfect_statedProj (k := descentField σ) hm hne
  haveI : IsSimpleGroup (StatedProj (StatedSp m (descentField σ))) := hs
  haveI : Group.IsPerfect (StatedProj (StatedSp m (descentField σ))) := hperf
  haveI : IsSimpleGroup ↥(fixSubgroup (fieldAut m K σ)) := e.isSimpleGroup
  haveI : Group.IsPerfect ↥(fixSubgroup (fieldAut m K σ)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hJeq : J = fixSubgroup (fieldAut m K σ) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.component_eq_of_fixed
      (Y := fixSubgroup (fieldAut m K σ)) hJ le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
      (Subgroup.commutator_le_self _)
  rw [hJeq]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv e

theorem nonempty_quotCenter_equiv_alternating_of_glaPComponent_fieldAut {p : ℕ} (hp : Odd p)
    {σ : K ≃+* K} (hσ : σ ^ p = 1) (hk : Nat.card (descentField σ) = 2)
    {J : Subgroup (StatedProj (StatedSp 2 K))}
    (hJ : GLAPComponent p (fixSubgroup (fieldAut 2 K σ)) J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* alternatingGroup (Fin 6)) := by
  haveI : NeZero 2 := ⟨by norm_num⟩
  obtain ⟨e⟩ := nonempty_fixSubgroup_fieldAut_equiv (m := 2) hp hσ
  have hE : ↥(fixSubgroup (fieldAut 2 K σ)) ≃* sympFour :=
    e.trans (statedProjEquivSympFour hk)
  set C := fixSubgroup (fieldAut 2 K σ) with hC
  have hmap : (commutator ↥C).map hE.toMonoidHom = commutator sympFour := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      hE.toMonoidHom.range_eq_top_of_surjective hE.surjective]
  let e₁ : ↥((commutator ↥C).map C.subtype) ≃* ↥(commutator sympFour) :=
    ((commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
      (((commutator ↥C).equivMapOfInjective hE.toMonoidHom hE.injective).trans
        (MulEquiv.subgroupCongr hmap))
  haveI : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
  haveI : Group.IsPerfect ↥(commutator sympFour) := isPerfect_commutator_sympFour
  haveI : IsSimpleGroup ↥((commutator ↥C).map C.subtype) := e₁.isSimpleGroup
  haveI : Group.IsPerfect ↥((commutator ↥C).map C.subtype) :=
    Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
  have hcomm : (commutator ↥C).map C.subtype = ⁅C, C⁆ := Subgroup.map_subtype_commutator C
  have hN : ((commutator ↥C).map C.subtype).subgroupOf C = commutator ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hYn : (((commutator ↥C).map C.subtype).subgroupOf C).Normal := by
    rw [hN]
    infer_instance
  have hJeq : J = (commutator ↥C).map C.subtype :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.component_eq_of_fixed
      (Y := (commutator ↥C).map C.subtype) hJ (Subgroup.map_subtype_le _) hYn hcomm.ge
  rw [hJeq]
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv
    (e₁.trans commutatorEquivAlternating)

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympComp

end
