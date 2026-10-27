module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (U3Config)

structure PointConfig (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (G : Type) [Group G] [Finite G] (p : ℕ)
    (P : Sylow p G) (M : Subgroup G) (x : G) (J : Subgroup G) : Prop where
  sigma : p ∈ rankThreeSigmaA G
  core : IsCoreMaxLocal p P M
  fail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M
  larger : LargerPrimesUnique G p
  generic : IsGenericPoint p P M x
  five : 5 ≤ p
  le_cent : J ≤ Subgroup.centralizer ({x} : Set G)
  cent_le : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G)
  perfect : Group.IsPerfect J
  lt : rankThreePrimeCore p J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
    N = rankThreePrimeCore p J ∨ N = J
  not_le : ¬ J ≤ M
  typ : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ Typ p Q

variable {G : Type} [Group G] [Finite G]

theorem PointConfig.prime {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} {x : G} {J : Subgroup G} (hc : PointConfig Typ G p P M x J) : p.Prime :=
  sigmaA_prime p hc.sigma

theorem pointConfig_of_u3 {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hc : U3Config G p P M x J) :
    PointConfig (fun p K _ => CFSG.LocalAnalysis.RankThreeTheoremC.IsU3Pred p K) G p P M x J :=
  ⟨hc.sigma, hc.core, hc.fail, hc.larger, hc.generic, hc.five, hc.le_cent, hc.cent_le, hc.perfect,
    hc.lt, hc.minimal, hc.not_le, hc.u3⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
