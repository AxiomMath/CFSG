module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog

theorem norm_of_gens {G : Type*} [Group G] [Finite G] (O : Subgroup G) {X : Set G}
    (h : ∀ x ∈ X, ∀ o ∈ O, x * o * x⁻¹ ∈ O) :
    ∀ c ∈ Subgroup.closure X, ∀ o ∈ O, c * o * c⁻¹ ∈ O := by
  have hX : Subgroup.closure X ≤ Subgroup.normalizer (O : Set G) := by
    refine (Subgroup.closure_le (Subgroup.normalizer (O : Set G))).mpr ?_
    intro x hx
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      obtain ⟨o, ho, rfl⟩ := hy
      exact h x hx o ho
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  intro c hc o ho
  exact (Subgroup.mem_normalizer_iff.mp (hX hc) o).mp ho

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
