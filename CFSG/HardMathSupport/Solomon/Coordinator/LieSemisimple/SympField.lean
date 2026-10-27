module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.Open (StatedProj StatedSp)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  isPerfect_commutator_sympFour)
open CFSG.RankThree.PartOne.KCSpComm (mem_spFixedGroup spFixedGroup_fieldAut_eq_range subfieldInj
  subfieldInj_injective range_subfieldInj simple_perfect_statedProj statedProjEquivSympFour)

private theorem exists_not_comm_of_simple_perfect {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hp : Group.IsPerfect Q) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  haveI := hs
  haveI := hp
  exact Group.IsPerfect.not_isSolvable Q
    (Group.isSolvable_of_comm fun a b => by_contra fun hab => h ⟨a, b, hab⟩)

private theorem perfectInLayer_of_mulEquiv_simple {S : Type*} [Group S] {β : MulAut S}
    {H : Type*} [Group H] (e : ↥(fixSubgroup β) ≃* H) (hs : IsSimpleGroup H)
    (hp : Group.IsPerfect H) : PerfectInLayer β := by
  haveI := hs
  haveI := hp
  have hsC : IsSimpleGroup ↥(fixSubgroup β) := e.isSimpleGroup
  have hpC : Group.IsPerfect ↥(fixSubgroup β) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact perfectInLayer_of_isSimpleGroup β hsC (exists_not_comm_of_simple_perfect hsC hpC)

private theorem perfectInLayer_of_mulEquiv_commutator {S : Type*} [Group S] {β : MulAut S}
    {H : Type*} [Group H] (e : ↥(fixSubgroup β) ≃* H) (hs : IsSimpleGroup ↥(commutator H))
    (hp : Group.IsPerfect ↥(commutator H)) : PerfectInLayer β := by
  have hmap : (commutator ↥(fixSubgroup β)).map e.toMonoidHom = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      e.toMonoidHom.range_eq_top_of_surjective e.surjective]
  let e₁ : ↥(commutator ↥(fixSubgroup β)) ≃* ↥(commutator H) :=
    (Subgroup.equivMapOfInjective (commutator ↥(fixSubgroup β)) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hqH : CFSG.IsQuasisimple ↥(commutator H) :=
    isQuasisimple_of_isSimpleGroup hs (exists_not_comm_of_simple_perfect hs hp)
  have hN : ((commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype).subgroupOf
      (fixSubgroup β) = commutator ↥(fixSubgroup β) :=
    Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective _
  haveI : (((commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype).subgroupOf
      (fixSubgroup β)).Normal := by
    rw [hN]
    infer_instance
  have hJq : CFSG.IsQuasisimple ↥((commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (commutator ↥(fixSubgroup β)) (fixSubgroup β).subtype
        (fixSubgroup β).subtype_injective).symm
      (CFSG.IsQuasisimple.of_mulEquiv e₁ hqH)
  haveI : IsMulCommutative (↥(fixSubgroup β) ⧸
      ((commutator ↥(fixSubgroup β)).map (fixSubgroup β).subtype).subgroupOf (fixSubgroup β)) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hN.ge
  exact perfectInLayer_of_normal_quasisimple (Subgroup.map_subtype_le _) hJq inferInstance

private theorem nonempty_fixSubgroup_equiv {r : ℕ} [NeZero r] {K : Type} [Field K] {p : ℕ}
    (hp : Odd p) {σ : K ≃+* K} (hσ : σ ^ p = 1) :
    Nonempty (↥(fixSubgroup (fieldAut r K σ)) ≃* StatedProj (StatedSp r (descentField σ))) := by
  have hfix : fixSubgroup (fieldAut r K σ) = (subfieldInj (r := r) σ).range := by
    rw [range_subfieldInj, ← spFixedGroup_fieldAut_eq_range hp hσ]
    exact Subgroup.ext fun x => mem_fixSubgroup.trans mem_spFixedGroup.symm
  exact ⟨(MulEquiv.subgroupCongr hfix).trans
    (MonoidHom.ofInjective (subfieldInj_injective (r := r) σ)).symm⟩

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem perfectInLayer_fieldAut_sp (hr : 2 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (σ : K ≃+* K) (hσ : σ ^ p = 1) : PerfectInLayer (fieldAut r K σ) := by
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨e⟩ := nonempty_fixSubgroup_equiv (r := r) (hp.odd_of_ne_two hp2) hσ
  by_cases hex : r = 2 ∧ Nat.card (descentField σ) = 2
  · obtain ⟨rfl, hk⟩ := hex
    exact perfectInLayer_of_mulEquiv_commutator (e.trans (statedProjEquivSympFour hk))
      isSimpleGroup_commutator_sympFour isPerfect_commutator_sympFour
  · obtain ⟨hs, hperf⟩ := simple_perfect_statedProj (k := descentField σ) hr hex
    exact perfectInLayer_of_mulEquiv_simple e hs hperf

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
