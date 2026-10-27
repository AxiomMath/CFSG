module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def KFactInvolution (S : ℕ → ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], S p K →
    ∀ Q : Sylow p K, 2 ≤ CFSG.Open.pRank p (Q : Subgroup K) ∧
      ∃ u ∈ (Subgroup.center ↥(Q : Subgroup K)).map (Q : Subgroup K).subtype, orderOf u = p ∧
        ∃ z : K, z ≠ 1 ∧ z ^ 2 = 1 ∧ z * u = u * z ∧
          Subgroup.closure ((Subgroup.centralizer ({z} : Set K) : Set K) ∪
            (Subgroup.normalizer ((Q : Subgroup K) : Set K) : Set K)) = ⊤

@[expose] def GL83GenericPlane (S : ℕ → ∀ (K : Type) [Group K], Prop) (G : Type) [Group G]
    [Finite G] : Prop :=
  GenericAt G fun p P M x => 5 ≤ p → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → S p Q →
      ¬ Nonempty (Q ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
      ∀ z : G, z ∈ J → z ≠ 1 → z ^ 2 = 1 → ∀ R : Subgroup G, R ≤ (P : Subgroup G) →
        IsElemAbelian p R → Nat.card R = p ^ 2 → x ∈ R →
        R ≤ Subgroup.centralizer ({z} : Set G) →
        CFSG.Open.pRank p (Subgroup.centralizer ({z} : Set G)) ≤ 2 →
        Subgroup.centralizer ({z} : Set G) ≤ M

@[expose] def IsU3Pred (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoLie K (.twistedA 2 q)

@[expose] def KFactU3Involution : Prop := KFactInvolution fun p K _ => IsU3Pred p K

@[expose] def GL83GenericU3Plane (G : Type) [Group G] [Finite G] : Prop :=
  GL83GenericPlane (fun p K _ => IsU3Pred p K) G

end CFSG.LocalAnalysis.RankThreeTheoremC
