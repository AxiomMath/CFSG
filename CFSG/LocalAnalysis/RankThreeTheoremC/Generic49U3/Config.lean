module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

structure U3Config (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x : G) (J : Subgroup G) : Prop where
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
  u3 : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore p J).subgroupOf J ∧ IsU3Pred p Q

variable {G : Type} [Group G] [Finite G]

theorem U3Config.prime {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G} {J : Subgroup G}
    (hc : U3Config G p P M x J) : p.Prime :=
  sigmaA_prime p hc.sigma

@[expose] def u3S {p : ℕ} (P : Sylow p G) (x : G) : Subgroup G :=
  (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)

@[expose] def u3T {p : ℕ} (P : Sylow p G) (x : G) (J : Subgroup G) : Subgroup G :=
  u3S P x ⊓ J

@[expose] def u3ZT {p : ℕ} (P : Sylow p G) (x : G) (J : Subgroup G) : Subgroup G :=
  u3T P x J ⊓ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G)

@[expose] def u3U0 {p : ℕ} (P : Sylow p G) (x : G) (J : Subgroup G) : Subgroup G :=
  u3ZT P x J ⊔ Subgroup.zpowers x

@[expose] def U3LineWC (y : G) (Q : Subgroup G) : Prop :=
  ∀ g : G, (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom ≤ Q →
    (Subgroup.zpowers y).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers y

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
