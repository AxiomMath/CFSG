module

public import CFSG.LocalAnalysis.OddStandard.ResidualOddLie
public import CFSG.LocalAnalysis.OddStandard.RouteWChildren
public import CFSG.LocalAnalysis.OddStandard.ChildHe
public import CFSG.LocalAnalysis.OddStandard.AltNoHe
import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.OddStandard.GlueL34

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def OddLieThm187b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ((∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) →
      ComponentClassification.OutcomeLocal.UOutcome G) →
    OddLieType (L ⧸ center L) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    ¬ HarrisSolomonFritzScope L →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

theorem oddLieCyclicBeyondHSF_of_faithful (h : OddLieThm187b)
    (hU : KProperSimpleUnbalancedUOutcome) : OddLieCyclicBeyondHSF :=
  fun G _ _ L hS => by
    have := hS.simple
    exact h G L hS (hU G hS.nonab hS.kProper)

@[expose] def RankTwoHeStandardO : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    ComponentClassification.RankTwoStandard.RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ →
    ¬ IsSporadic (ComponentClassification.RankTwoStandard.rankTwoQuot A) .He

theorem rankTwoHeStandardO_of_rankTwoHeStandard (h : RankTwoHeStandard) : RankTwoHeStandardO :=
  fun G _ _ A hA _ => h G A hA

theorem childHeW_of_casesO
    (hMult : ComponentClassification.TBLit.HeldTrivialMultiplier)
    (hRank : RankTwoHeStandardO)
    (hU : KProperSimpleUnbalancedUOutcome)
    (hBal : HeStandardBalanced) : ChildHeW := by
  intro G _ _ L hS hHe
  have := hS.simple
  have hstd := hS.standard
  by_cases hUo : ComponentClassification.OutcomeLocal.UOutcome G
  ·
    have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
      ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
    let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
      ComponentClassification.GSLit.generalizedFittingEquivOfSimple
    rcases hUo with h | ⟨n, hodd, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩
    · exact (ClassicalInvolution.oddLieType_congr e).1 h
    · exact (altNoStandardHe G hS.nonab n hodd h7 (fun h4 => (h1 h4).ne htop)
        ⟨e.symm.trans eA⟩ L hstd hHe).elim
    · exact absurd htop hlt.ne
  ·
    have hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := by
      intro z hz
      by_contra hne
      exact hUo (hU G hS.nonab hS.kProper ⟨z, hz, hne⟩)
    have hrank : ¬ 2 ≤ Open.pRank 2 (centralizer (L : Set G)) := fun h2 =>
      hRank G L (GlueL34.rankTwoHyp hS h2) (GlueL34.oddCore_eq_bot hS) hHe
    have hq : CFSG.IsQuasisimple L :=
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hstd.1
    have hZ : center L = ⊥ := hMult L hq hHe
    exact (hBal G hS.nonab hS.kProper hUo hbal L hstd hHe hZ hrank).elim

end CFSG.OddStandard
