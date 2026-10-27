module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem psiBase_injective {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo) :
    Function.Injective (psiBase Q e) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective y
  change e (QuotientGroup.mk (g : C)) = e (QuotientGroup.mk (g' : C)) at hxy
  have h1 : (QuotientGroup.mk (g : C) : C ⧸ Q) = QuotientGroup.mk (g' : C) := e.injective hxy
  rw [QuotientGroup.eq] at h1
  rw [QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf.mpr h1

theorem range_psiBase {C : Type} [Group C] {Q : Subgroup C} [Q.Normal] (e : C ⧸ Q ≃* A5WrTwo) :
    (psiBase Q e).range = commutator A5WrTwo := by
  rw [← A5WrTwo.range_baseEmb]
  apply le_antisymm
  · rintro p ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    simpa only [psiBase_mk] using (mem_baseSub_iff e).mp g.2
  · intro p hp
    obtain ⟨q, rfl⟩ := hp
    obtain ⟨y, hy⟩ := e.surjective (A5WrTwo.baseEmb q)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨QuotientGroup.mk ⟨g, ?_⟩, ?_⟩
    · rw [mem_baseSub_iff, hy]
      exact ⟨q, rfl⟩
    · rw [psiBase_mk, hy]

theorem nonempty_quot_baseSub {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (e : C ⧸ Q ≃* A5WrTwo) :
    Nonempty (↥(baseSub Q e) ⧸ Q.subgroupOf (baseSub Q e) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  refine ⟨(MonoidHom.ofInjective (psiBase_injective e)).trans ?_⟩
  exact (MulEquiv.subgroupCongr ((range_psiBase e).trans A5WrTwo.range_baseEmb.symm)).trans
    (MonoidHom.ofInjective (f := A5WrTwo.baseEmb) A5WrTwo.baseEmb_injective).symm

end CFSG.EvenSporadicStandard.HNRecog.Section3
