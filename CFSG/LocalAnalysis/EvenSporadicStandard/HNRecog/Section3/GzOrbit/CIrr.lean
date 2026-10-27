module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

private lemma priv_conj_eq_commutatorElement_mul {G : Type*} [Group G] (y w : G) :
    y * w * y⁻¹ = ⁅y, w⁆ * w := by
  rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]

theorem cIrreducible_of_exists_shape (hD : AschbacherDichotomy) {C : Type} [Group C] [Finite C]
    {Q : Subgroup C} [Q.Normal] (hQ : IsExtraspecialPlusByA5WrTwoWith C Q) {q : C} (hqQ : q ∈ Q)
    (hq : q ∉ centerOf Q) (hsh : IsShapeTwoTwoSixS5 ↥(Subgroup.centralizer ({q} : Set C))) :
    CIrreducible C Q := by
  obtain ⟨e⟩ := hQ.quotient
  obtain ⟨S, hS, hSiso⟩ := exists_stabilizer_alternating hQ e hqQ hq hsh
  set q' : ↥(baseSub Q e) := ⟨q, le_baseSub e hqQ⟩ with hq'def
  have hq'Q : q' ∈ Q.subgroupOf (baseSub Q e) := Subgroup.mem_subgroupOf.mpr hqQ
  have hq'Z : q' ∉ centerOf (Q.subgroupOf (baseSub Q e)) :=
    fun hx => hq ((mem_centerOf_subgroupOf_baseSub_iff e q').mp hx)
  have hirrL := (hD ↥(baseSub Q e) (Q.subgroupOf (baseSub Q e))
      (isPlusExtraspecial_subgroupOf_baseSub hQ e)
      (centralizer_subgroupOf_baseSub_le hQ e)
      (nonempty_quot_baseSub e)).mpr
    ⟨q', hq'Q, hq'Z, S, hS, hSiso⟩
  intro W hZ hW hinv
  have hZ' : centerOf (Q.subgroupOf (baseSub Q e)) ≤ W.subgroupOf (baseSub Q e) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hZ ((mem_centerOf_subgroupOf_baseSub_iff e x).mp hx))
  have hW' : W.subgroupOf (baseSub Q e) ≤ Q.subgroupOf (baseSub Q e) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hW (Subgroup.mem_subgroupOf.mp hx))
  have hinv' : ∀ g : ↥(baseSub Q e), ∀ w ∈ W.subgroupOf (baseSub Q e),
      g * w * g⁻¹ ∈ W.subgroupOf (baseSub Q e) := by
    intro g w hw
    obtain ⟨c, hc, y, hy, hgy⟩ := (baseSub_eq_commutator_mul e).2 (g : C) g.2
    have hwW : (w : C) ∈ W := Subgroup.mem_subgroupOf.mp hw
    have hyw : y * (w : C) * y⁻¹ ∈ W := by
      rw [priv_conj_eq_commutatorElement_mul]
      exact W.mul_mem (hZ (commutatorElement_mem_centerOf hQ.plus hy (hW hwW))) hwW
    have hconj : c * (y * (w : C) * y⁻¹) * c⁻¹ ∈ W := hinv c hc _ hyw
    refine Subgroup.mem_subgroupOf.mpr ?_
    change (g : C) * (w : C) * (g : C)⁻¹ ∈ W
    rw [hgy]
    convert hconj using 1
    group
  rcases hirrL (W.subgroupOf (baseSub Q e)) hZ' hW' hinv' with h | h
  · left
    apply le_antisymm _ hZ
    intro w hw
    have hw' : (⟨w, le_baseSub e (hW hw)⟩ : ↥(baseSub Q e)) ∈ W.subgroupOf (baseSub Q e) :=
      Subgroup.mem_subgroupOf.mpr hw
    rw [h] at hw'
    exact (mem_centerOf_subgroupOf_baseSub_iff e ⟨w, le_baseSub e (hW hw)⟩).mp hw'
  · right
    apply le_antisymm hW
    intro y hy
    have hy' : (⟨y, le_baseSub e hy⟩ : ↥(baseSub Q e)) ∈ Q.subgroupOf (baseSub Q e) :=
      Subgroup.mem_subgroupOf.mpr hy
    rw [← h] at hy'
    exact Subgroup.mem_subgroupOf.mp hy'

end CFSG.EvenSporadicStandard.HNRecog.Section3
