module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def hyp111Pre (p : ℕ) (H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Subgroup G :=
  (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype

structure AGL81ElevenData (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  escape : ∃ H₁ R₁ : Subgroup G, D1Escape p P M H₁ R₁
  maxH : GLBIsMaxTwoLocal H
  pair : AGLHyp111Pair p M H Q K
  kbar : K = d1KBar p M H
  b3 : Hyp111B3 p H Q K
  sylowK : ∃ S : Sylow p K, (S : Subgroup K).map K.subtype =
    (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ K
  star : ∀ R : Subgroup G, IsMaxInvariantTwoIn Q R (d1PlusCore p H K) → R ≠ ⊥ →
    CFSG.Quasithin.CGS R ≤ H ∧ CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo Q R

@[expose] def AGL81ElevenFiveAt (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81ElevenData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    (Open.pRank p K ≤ 1 → 3 ≤ Open.pRank p H) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      p = 3 ∧ IsComponentOf K ⊤ ∧
        ((IsAltTwoP 3 K ∧ ∃ I₀ ∈ cZero (H ⊓ L),
            CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre p H K) ∨
          (IsLinThreeFour K ∧ IsAGLQ 3 M (d1LiftX p H Q K) ∧
            ¬ Hyp111B3 p H (d1LiftX p H Q K) K))

@[expose] def AGL81NineEightFour (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H₁ R₁ : Subgroup G), D1Escape p P M H₁ R₁ →
    ∀ H₀ Q₀ : Subgroup G, IsAGLQ p M Q₀ → Q₀ ≤ H₀ → GLBIsMaxTwoLocal H₀ → ¬ H₀ ≤ M →
    (∃ S : Sylow p (d1KBar p M H₀), (S : Subgroup (d1KBar p M H₀)).map (d1KBar p M H₀).subtype =
      (Q₀.subgroupOf H₀).map (QuotientGroup.mk' (primeComplementCore (G := H₀) p)) ⊓
        d1KBar p M H₀) →
    Hyp111B3 p H₀ Q₀ (d1KBar p M H₀) →
    pCoreOf 2 (H₀ ⊓ M) = pCoreOf 2 H₀ ∧ pCoreOf 2 M ≤ pCoreOf 2 H₀ ∧ pCoreOf 2 H₀ ≤ M

@[expose] def AGL81TenFourteenTwoThree (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H₁ R₁ : Subgroup G), D1Escape 3 P M H₁ R₁ →
    ∀ a : G, a ∈ M → orderOf a = 3 → ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ 3 M U) →
    ∀ I : Subgroup G, IsTwoPrimeComponent (Subgroup.centralizer ({a} : Set G) ⊓ M) I →
      ¬ 3 ∣ Nat.card I

end CFSG.LocalAnalysis.RankThreeTheoremC
