module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def baseSub {C : Type} [Group C] (Q : Subgroup C) [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo) :
    Subgroup C :=
  A5WrTwo.baseEmb.range.comap ((e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q))

theorem mem_baseSub_iff {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo)
    {g : C} : g ∈ baseSub Q e ↔ e (QuotientGroup.mk g) ∈ A5WrTwo.baseEmb.range := Iff.rfl

theorem le_baseSub {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo) :
    Q ≤ baseSub Q e := by
  intro g hg
  rw [mem_baseSub_iff]
  have h1 : (QuotientGroup.mk g : C ⧸ Q) = 1 := (QuotientGroup.eq_one_iff g).2 hg
  rw [h1, map_one]
  exact one_mem _

@[expose] def psiBase {C : Type} [Group C] (Q : Subgroup C) [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo) :
    ↥(baseSub Q e) ⧸ Q.subgroupOf (baseSub Q e) →* A5WrTwo :=
  QuotientGroup.lift (Q.subgroupOf (baseSub Q e))
    (((e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)).comp (baseSub Q e).subtype) (by
      intro g hg
      have h1 : (QuotientGroup.mk (g : C) : C ⧸ Q) = 1 := (QuotientGroup.eq_one_iff _).2 hg
      simp [h1])

theorem psiBase_mk {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo)
    (g : ↥(baseSub Q e)) :
    psiBase Q e (QuotientGroup.mk g) = e (QuotientGroup.mk (g : C)) := rfl

theorem mem_centerOf_subgroupOf_baseSub_iff {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (e : C ⧸ Q ≃* A5WrTwo) (x : ↥(baseSub Q e)) :
    x ∈ centerOf (Q.subgroupOf (baseSub Q e)) ↔ (x : C) ∈ centerOf Q := by
  constructor
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    intro y hy
    have := hxc ⟨y, le_baseSub e hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
    exact congrArg Subtype.val this
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hxQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    intro y hy
    have := hxc (y : C) (Subgroup.mem_subgroupOf.mp hy)
    exact Subtype.ext this

end CFSG.EvenSporadicStandard.HNRecog.Section3
