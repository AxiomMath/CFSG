module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem commutatorElement_mem_centerOf {C : Type*} [Group C] {Q : Subgroup C}
    (hQ : IsPlusExtraspecial 4 Q) {y w : C} (hy : y ∈ Q) (hw : w ∈ Q) :
    ⁅y, w⁆ ∈ centerOf Q := by
  have hExt : CFSG.IsExtraspecial 2 ↥Q := hQ.1
  have hcomm : _root_.commutator ↥Q ≤ Subgroup.center ↥Q := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    haveI := hExt.quotient_elementary_abelian
    infer_instance
  have hc : ⁅(⟨y, hy⟩ : ↥Q), (⟨w, hw⟩ : ↥Q)⁆ ∈ Subgroup.center ↥Q :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem hy hw) (Q.inv_mem hy)) (Q.inv_mem hw)
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
    exact congrArg Subtype.val h1

theorem conj_mem_centerOf {C : Type*} [Group C] {Q : Subgroup C} [Q.Normal] {x : C}
    (hx : x ∈ centerOf Q) (t : C) : t * x * t⁻¹ ∈ centerOf Q := by
  obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨Subgroup.Normal.conj_mem inferInstance x hxQ t, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hxc ⊢
  intro h hh
  have hh' : t⁻¹ * h * t ∈ Q := by
    have := Subgroup.Normal.conj_mem (inferInstance : Q.Normal) h hh t⁻¹
    simpa using this
  have h1 := hxc _ hh'
  calc h * (t * x * t⁻¹) = t * ((t⁻¹ * h * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * h * t)) * t⁻¹ := by rw [h1]
    _ = (t * x * t⁻¹) * h := by group

end CFSG.EvenSporadicStandard.HNRecog.Section3
