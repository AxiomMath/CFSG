module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.Adapters.TauCetiLieModels
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.ClassicalRankOne
import CFSG.LocalAnalysis.QuasithinUnique.K1.Alt
import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalSuzuki
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.GroupTheory

theorem IsGomiL2.fusionIsBenderGroup {Y : Type} [Group Y] (h : IsGomiL2 Y) :
    CFSG.Open.fusionIsBenderGroup Y := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨_, hv⟩, ⟨q, hq, rfl⟩, ⟨e⟩⟩
  · exact CFSG.QuasithinUnique.K1.Alt.alternating_five_isBender e
  · have hm : CFSG.Open.StatedClassicalModel Y .PSL 2 q.p q.exponent :=
      (CFSG.Models.lieModel_A 1 q hv e).2.resolve_right fun h => absurd h.1 (by norm_num)
    rw [hq] at hm
    exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSL_two
      hm

theorem IsGomiU3.fusionIsBenderGroup {Y : Type} [Group Y] (h : IsGomiU3 Y) :
    CFSG.Open.fusionIsBenderGroup Y := by
  obtain ⟨⟨_, hv⟩, ⟨q, hq, rfl⟩, ⟨e⟩⟩ := h
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hq] at hm
  exact CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fusionIsBenderGroup_of_statedPSU_three
    hm

theorem IsGomiSz.fusionIsBenderGroup {Y : Type} [Group Y] (h : IsGomiSz Y) :
    CFSG.Open.fusionIsBenderGroup Y := by
  obtain ⟨⟨_, hv⟩, ⟨k, rfl⟩, ⟨e⟩⟩ := h
  exact CFSG.QuasithinUnique.K1.fusionIsBenderGroup_of_mulEquiv_tcSuzuki hv e

theorem fusionIsBenderGroup_of_isGomiRankOne {Y : Type} [Group Y]
    (h : IsGomiL2 Y ∨ IsGomiU3 Y ∨ IsGomiSz Y) : CFSG.Open.fusionIsBenderGroup Y :=
  h.elim IsGomiL2.fusionIsBenderGroup
    fun h => h.elim IsGomiU3.fusionIsBenderGroup IsGomiSz.fusionIsBenderGroup

end CFSG.GroupTheory
