module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open scoped commutatorElement

variable {S : Type*} [Group S]

theorem perfectInLayer_congr_fix {β β' : MulAut S} (h : fixSubgroup β = fixSubgroup β') :
    PerfectInLayer β ↔ PerfectInLayer β' := by
  unfold PerfectInLayer
  rw [h]

theorem fixSubgroup_inv_eq (β : MulAut S) : fixSubgroup β⁻¹ = fixSubgroup β := by
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup]
  constructor
  · intro h
    have h1 : β (β⁻¹ x) = β x := congrArg (fun y => β y) h
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm
  · intro h
    have h1 : β⁻¹ (β x) = β⁻¹ x := congrArg (fun y => β⁻¹ y) h
    rw [MulAut.inv_apply_self] at h1
    exact h1.symm

theorem perfectInLayer_inv_iff (β : MulAut S) : PerfectInLayer β⁻¹ ↔ PerfectInLayer β :=
  perfectInLayer_congr_fix (fixSubgroup_inv_eq β)

theorem perfectInLayer_of_isQuasisimple_fixSubgroup (β : MulAut S)
    (h : CFSG.IsQuasisimple ↥(fixSubgroup β)) : PerfectInLayer β := by
  haveI : ((fixSubgroup β).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  haveI : Subsingleton (↥(fixSubgroup β) ⧸ (fixSubgroup β).subgroupOf (fixSubgroup β)) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)
  exact perfectInLayer_of_normal_quasisimple (J := fixSubgroup β) le_rfl h inferInstance

theorem perfectInLayer_of_isSimpleGroup_commutator (β : MulAut S)
    (hs : IsSimpleGroup ↥(commutator ↥(fixSubgroup β))) : PerfectInLayer β := by
  haveI := hs
  by_cases hnc : ∃ a b : ↥(commutator ↥(fixSubgroup β)), a * b ≠ b * a
  · set C := fixSubgroup β with hC
    set D : Subgroup ↥C := commutator ↥C with hD
    set J : Subgroup S := D.map C.subtype with hJ
    have hJC : J ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hJD : J.subgroupOf C = D :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective D
    haveI : (J.subgroupOf C).Normal := by
      rw [hJD]
      infer_instance
    let e : ↥D ≃* ↥J := D.equivMapOfInjective C.subtype C.subtype_injective
    haveI : IsSimpleGroup ↥D := hs
    have hsJ : IsSimpleGroup ↥J := e.symm.isSimpleGroup
    have hncJ : ∃ a b : ↥J, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnc
      exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
    have hJq : CFSG.IsQuasisimple ↥J := isQuasisimple_of_isSimpleGroup hsJ hncJ
    have hsol : Group.IsSolvable (↥C ⧸ J.subgroupOf C) := by
      refine isSolvable_of_comm fun x y => ?_
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hJD]
      have h1 : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [h1]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact perfectInLayer_of_normal_quasisimple hJC hJq hsol
  · push Not at hnc
    refine perfectInLayer_of_isSolvable_fixSubgroup β ⟨2, ?_⟩
    rw [derivedSeries_succ, derivedSeries_one, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hnc ⟨y, hy⟩ ⟨x, hx⟩)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
