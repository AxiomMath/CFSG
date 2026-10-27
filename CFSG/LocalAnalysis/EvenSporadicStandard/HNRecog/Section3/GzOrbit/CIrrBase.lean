module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem baseSub_eq_commutator_mul {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (e : C ⧸ Q ≃* A5WrTwo) :
    commutator C ≤ baseSub Q e ∧ ∀ g ∈ baseSub Q e, ∃ c ∈ commutator C, ∃ y ∈ Q, g = c * y := by
  let π : C →* A5WrTwo := (e : C ⧸ Q →* A5WrTwo).comp (QuotientGroup.mk' Q)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hmapC : (commutator C).map π = commutator A5WrTwo := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective π hπ]
    rfl
  have hmem : ∀ c ∈ commutator C, π c ∈ A5WrTwo.baseEmb.range := by
    intro c hc
    rw [A5WrTwo.range_baseEmb, ← hmapC]
    exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
  constructor
  · intro c hc
    rw [mem_baseSub_iff]
    exact hmem c hc
  · intro g hg
    rw [mem_baseSub_iff] at hg
    have h2 : π g ∈ (commutator C).map π := by
      rw [hmapC, ← A5WrTwo.range_baseEmb]
      exact hg
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp h2
    refine ⟨c, hc, c⁻¹ * g, ?_, (mul_inv_cancel_left c g).symm⟩
    rw [← QuotientGroup.eq_one_iff, ← (MulEquiv.map_eq_one_iff e)]
    have h1 : π (c⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hcg, inv_mul_cancel]
    exact h1

end CFSG.EvenSporadicStandard.HNRecog.Section3
