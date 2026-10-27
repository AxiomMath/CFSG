module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Extraspecial.Quotient

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.centerOf_le_center [Finite C] (hC : AschbacherHyp C Q) :
    centerOf Q ≤ Subgroup.center C := by
  have hE : IsExtraspecialPGroup 2 Q := hC.plus.isExtraspecialPGroup
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · have hzQ : z ∈ Q := by
      have h := hz
      rw [centerOf] at h
      exact h.1
    let z' : Q := ⟨z, hzQ⟩
    have hz'c : z' ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_inf.mp (show z ∈ Q ⊓ centralizer (Q : Set C) from hz)).2
        (y : C) y.2
    let w : Q := ⟨g * z * g⁻¹, (inferInstance : Q.Normal).conj_mem z hzQ g⟩
    have hwc : w ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      change (y : C) * (g * z * g⁻¹) = (g * z * g⁻¹) * (y : C)
      have hu_mem : g⁻¹ * (y : C) * g ∈ Q := by
        simpa using (inferInstance : Q.Normal).conj_mem (y : C) y.2 g⁻¹
      have hzu := Subgroup.mem_center_iff.mp hz'c ⟨g⁻¹ * (y : C) * g, hu_mem⟩
      have hzuC : (g⁻¹ * (y : C) * g) * z = z * (g⁻¹ * (y : C) * g) :=
        congrArg Subtype.val hzu
      calc (y : C) * (g * z * g⁻¹)
          = g * ((g⁻¹ * (y : C) * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * (y : C) * g)) * g⁻¹ := by rw [hzuC]
        _ = (g * z * g⁻¹) * (y : C) := by group
    have hz'ne : z' ≠ 1 := by
      intro h
      exact hz1 (congrArg Subtype.val h)
    have hwne : w ≠ 1 := by
      intro h
      apply hz1
      have hval : g * z * g⁻¹ = 1 := by
        simpa only [Subgroup.coe_one, Subgroup.coe_mul] using congrArg Subtype.val h
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hval]
        _ = 1 := by group
    have hzw : z' = w :=
      CFSG.RankThree.Literature.FSmith.eq_of_mem_center hE hz'c hwc hz'ne hwne
    have hgz : g * z * g⁻¹ = z := by
      have h := congrArg Subtype.val hzw
      exact h.symm
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hgz]

end CFSG.EvenSporadicStandard.HNRecog
