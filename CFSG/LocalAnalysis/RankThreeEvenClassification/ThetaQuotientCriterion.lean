module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ElementaryPlanes

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def CentralLineThetaCriterion {G : Type u} [Group G] (prime : ℕ) (actor : Subgroup G) : Prop :=
  ∀ element ∈ actor, element ≠ 1 →
    ∀ (lineNormal : (Subgroup.zpowers (elementInCentralizer element)).Normal),
      let quotient := @QuotientGroup.mk' (Subgroup.centralizer ({element} : Set G))
        _ (Subgroup.zpowers (elementInCentralizer element)) lineNormal
      thetaPlaneAlpha prime ((actor.subgroupOf
        (Subgroup.centralizer ({element} : Set G))).map quotient) ≤
        solvablePrimeComplementCore
          ((Subgroup.centralizer ({element} : Set G)) ⧸
            Subgroup.zpowers (elementInCentralizer element)) prime

theorem CentralLineThetaCriterion.raw_plane_containment {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (hcriterion : CentralLineThetaCriterion prime actor)
    (element : G) (hmem : element ∈ actor) (hne : element ≠ 1) (plane : Subgroup G)
    (hplaneLe : plane ≤ actor) (hplaneCard : Nat.card plane = prime ^ 2) :
    thetaPlaneAlpha prime (plane.subgroupOf (Subgroup.centralizer ({element} : Set G))) ≤
      solvablePrimeComplementCore (Subgroup.centralizer ({element} : Set G)) prime := by
  exact rank_three_central_line_raw_plane_containment prime hprime actor hab hactorCard
    element hmem hne plane hplaneLe hplaneCard (hcriterion element hmem hne)

theorem CentralLineThetaCriterion.mixed_balance {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (hcriterion : CentralLineThetaCriterion prime actor)
    (first second : G) (hfirst : first ∈ actor) (hsecond : second ∈ actor)
    (hfirstNe : first ≠ 1) (hsecondNe : second ≠ 1) :
    ⁅Subgroup.centralizer ({second} : Set G) ⊓
      thetaCoreOf prime (Subgroup.centralizer ({first} : Set G)), actor⁆ ≤
        thetaCoreOf prime (Subgroup.centralizer ({second} : Set G)) := by
  exact theta_mixed_balance_of_rank_three_local_planes prime hprime actor hab hactorCard
    (CentralLineThetaCriterion.raw_plane_containment prime hprime actor hab hactorCard hcriterion)
    first second hfirst hsecond hfirstNe hsecondNe

theorem CentralLineThetaCriterion.solvable_signalizer {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor : Subgroup G) (hab : IsElemAbelian prime actor)
    (hactorCard : Nat.card actor = prime ^ 3) (hcriterion : CentralLineThetaCriterion prime actor) :
    IsSolvableSignalizerFunctor prime actor (thetaActorSignalizer prime actor) := by
  exact thetaActorSignalizer_of_rank_three_local_planes prime hprime actor hab hactorCard
    (CentralLineThetaCriterion.raw_plane_containment prime hprime actor hab hactorCard hcriterion)

end CFSG.RankThreeEvenClassification.Helpers
