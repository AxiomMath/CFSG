module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Assemble

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.RuSchreier
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem center_eq_bot_of_isSporadic_ru
    {Y : Type} [Group Y] (hY : IsSporadic Y .Ru) : center Y = ⊥ := by
  obtain ⟨e⟩ := CFSG.EvenSporadicStandard.TwoRu.nonempty_mulEquiv_ruP_of_isSporadic hY
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ Subgroup.center ruP := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [center_ruP, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

end CFSG.EvenSporadicStandard.RuStd
