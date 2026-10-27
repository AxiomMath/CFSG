module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Facts
public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
import CFSG.LocalAnalysis.OddStandard.ResidualOddLie
import CFSG.GH74.Orders.Sporadic

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3Interfaces

theorem oddLieType_or_cyclic
    (hOdd : ComponentClassification.RankTwoStandard.RankTwoOddLieStandard)
    (hCI : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hS : StandardSetting G L)
    (hQ : SmallF3LieQuotient (L ⧸ center L)) :
    OddLieType G ∨
      ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) := by
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  have hlie : OddLieType (L ⧸ center L) := oddLieType hQ
  have h5 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) :=
    fun h => not_nonempty_mulEquiv_alternatingGroup hQ 5 h
  have h6 : ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) :=
    fun h => not_nonempty_mulEquiv_alternatingGroup hQ 6 h
  have h8 : ¬ Assembly.LowTwoRank.StatedClassicalModel (L ⧸ center L) .PSL 2 2 3 :=
    not_statedClassicalModel_psl_two_eight hQ
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S₀ with hrank | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · exfalso
    have hH : ComponentClassification.RankTwoStandard.RankTwoHyp G L :=
      ⟨hS.kProper, hS.standard, hS.not_normal, hrank⟩
    have hO : Open.standardComponentOddCore G = ⊥ := hS.oddCore_eq_bot
    exact (hOdd G L hH hO ⟨hlie, h5, h6, h8⟩).elim
  · right
    intro S
    exact ((Sylow.equiv S S₀).isCyclic).2 hcyc
  · rcases quaternion_oddLie_or_M12 hCI hS S₀ hr hq with h | h
    · exact Or.inl h
    · exfalso
      have hcard : Nat.card G = 2 ^ 6 * 3 ^ 3 * 5 * 11 :=
        CFSG.GH74.card_of_isSporadic_M12 h
      have hdiv1 : Nat.card (L ⧸ center L) ∣ Nat.card L :=
        Subgroup.card_quotient_dvd_card (Subgroup.center L)
      have hdiv2 : Nat.card L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
      rw [hcard] at hdiv2
      exact not_card_dvd_card_M12 hQ (hdiv1.trans hdiv2)

end CFSG.OddStandard.SmallF3
