module

public import CFSG.LocalAnalysis.OddStandard.RouteWFaithful
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def AltStdCyclicBalancedFalse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) →
          (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) → False

theorem altStdCyclicW_of_balancedFalse
    (hU : KProperSimpleUnbalancedUOutcome) (hB : AltStdCyclicBalancedFalse) : AltStdCyclicW := by
  intro G _ _ L hS n hn hθ S hcyc
  obtain ⟨θ⟩ := hθ
  have := hS.simple
  by_cases hz : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥
  · have hUO := hU G hS.nonab hS.kProper hz
    have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
      ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
    let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
      ComponentClassification.GSLit.generalizedFittingEquivOfSimple
    rcases hUO with hlie | ⟨m, -, -, ⟨θ'⟩, -⟩ | ⟨-, hlt⟩
    · exact Or.inr ((CFSG.ClassicalInvolution.oddLieType_congr e).1 hlie)
    · exact (altStandard_in_alternating (e.symm.trans θ') hS.standard hn θ S hcyc).elim
    · exact absurd htop hlt.ne
  · push Not at hz
    exact (hB G L hS n hn ⟨θ⟩ S hcyc hz).elim

theorem alternatingStandardFormInputW_of_balancedFalse
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hU : KProperSimpleUnbalancedUOutcome) (hB : AltStdCyclicBalancedFalse) :
    AlternatingStandardFormInputW :=
  alternatingStandardFormInputW_of_rankOne hRank2
    (altStdRankOneW_of_cyclicW hCIT (altStdCyclicW_of_balancedFalse hU hB))

end CFSG.OddStandard
