module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lA5Cover
public import CFSG.GH74.Uniqueness.SU.KI6BRankOne

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.ComponentClassification

theorem a2l_isSLTwoOver_five_of_isSL25 {X : Type} [Group X] (h : GH74.Uniqueness.SU.K.IsSL25 X) :
    HarrisLit.IsSLTwoOver 5 X := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  have hFt : Fintype F := Fintype.ofFinite F
  exact ⟨F, hF, hFt, by rw [← Nat.card_eq_fintype_card]; exact hcard,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm⟩⟩

theorem twoAnSL25_holds : HypA2.TwoAnSL25 := by
  intro Y _ _ n hn hY
  obtain ⟨hQ, hcard, he⟩ := hY
  have hTwo : GH74.Uniqueness.SU.K.IsTwoAlt Y n := ⟨hQ, inferInstance, hcard, he⟩
  obtain ⟨π, hπ⟩ := GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt hTwo
  obtain ⟨N, hkerN, hNq, hNr, hNc, hNe⟩ := a2l_preimage_a5 hπ (by omega)
  refine ⟨N, (hπ.center_eq_ker (by omega)).le.trans hkerN, ?_⟩
  exact a2l_isSLTwoOver_five_of_isSL25
    (GH74.Uniqueness.SU.K.R6.rankOne_sl25 ↥N hNq hNr hNc hNe)

end CFSG.OddStandard.SmallF3.HypA2Leaves
