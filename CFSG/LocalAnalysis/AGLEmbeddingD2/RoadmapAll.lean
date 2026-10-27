module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TorusCase

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open
open CFSG.AGLEmbedding

theorem d2IndexCaseAt_of_pRank {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) → ∀ p, Pp p →
      3 ≤ Open.pRank p (⊤ : Subgroup K)) : D2IndexCaseAt i Pp := by
  intro G _ _ _ _ p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
  exact hK.false_of_three_le_pRank (h K he p hp)

@[expose] def KFactSeitzRankThreeExceptions : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
      (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q)) →
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → 3 ≤ Open.pRank 3 (⊤ : Subgroup K)

theorem d2ComponentCase_of_all (hrank : KFactLieCharRank) (hS : D2SeitzCross)
    (hSch : KFactCatalogSchreier) (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hAlt5 : D2AltFive) (hA6 : D2AltSixCase) (hThree : D2U3Three)
    (HB : TauCeti.CFSGIndex → ℕ → Prop) (hHB : ∀ i, D2HeisBorelAt i (HB i))
    (hHB5 : ∀ i p, HB i p → 5 ≤ p)
    (TB : TauCeti.CFSGIndex → ℕ → Prop) (hTB : ∀ i, D2TorusBorelAt i (TB i))
    (hTB5 : ∀ i p, TB i p → 5 ≤ p)
    (RK : TauCeti.CFSGIndex → ℕ → Prop)
    (hRK : ∀ (i : TauCeti.CFSGIndex) (K : Type) [Group K] [Finite K], Nonempty (K ≃* i.Group) →
      ∀ p, RK i p → 3 ≤ Open.pRank p (⊤ : Subgroup K))
    (hexc : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p =>
        IsD2SeitzException p d.1 ∧ ¬ HB (.lie d) p ∧ ¬ TB (.lie d) p ∧ ¬ RK (.lie d) p)
    (hSpor : ∀ s : TauCeti.SporadicName,
      D2IndexCaseAt (.sporadic s) fun p =>
        ¬ HB (.sporadic s) p ∧ ¬ TB (.sporadic s) p ∧ ¬ RK (.sporadic s) p) :
    D2ComponentCase := by
  refine d2ComponentCase_of_families' hrank hS hSch hα h84 h85 h86 h93 hCGT hD2 hK2 hC3 hK5 hKin hKP
    hC3p hK5p hAlt5 hA6 hThree HB hHB hHB5 TB hTB hTB5 (fun d => ?_) fun s => ?_
  · intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
    by_cases hR : RK (.lie d) p
    · exact d2IndexCaseAt_of_pRank (hRK (.lie d)) G hglob hD1 p hR P M A H R hesc hmax hβ Rbar K
        hRbar hK he
    · exact hexc d G hglob hD1 p ⟨hp.1, hp.2.1, hp.2.2, hR⟩ P M A H R hesc hmax hβ Rbar K hRbar hK
        he
  · intro G _ _ hglob hD1 p hp P M A H R hesc hmax hβ Rbar K hRbar hK he
    by_cases hR : RK (.sporadic s) p
    · exact d2IndexCaseAt_of_pRank (hRK (.sporadic s)) G hglob hD1 p hR P M A H R hesc hmax hβ Rbar
        K hRbar hK he
    · exact hSpor s G hglob hD1 p ⟨hp.1, hp.2, hR⟩ P M A H R hesc hmax hβ Rbar K hRbar hK he

end CFSG.AGLEmbeddingD2
