module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def IsRankThreeU3 (K : Type) [Group K] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ IsoLie K (.twistedA 2 q)

structure IsU3Normal {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (J : Subgroup G) : Prop where
  le_centralizer : J ≤ centralizer ({x} : Set G)
  centralizer_le : centralizer ({x} : Set G) ≤ normalizer (J : Set G)
  perfect : Group.IsPerfect J
  not_le : ¬ J ≤ M
  lt_core : rankThreePrimeCore 3 J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore 3 J ≤ N →
    N = rankThreePrimeCore 3 J ∨ N = J
  iso : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore 3 J).subgroupOf J ∧ IsRankThreeU3 Q

@[expose] def U3Prop34 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧
  Nat.card ((P : Subgroup G) ⊓ J : Subgroup G) = p ^ 3 ∧
  (∀ t ∈ (P : Subgroup G) ⊓ J, t ^ p = 1) ∧
  ¬ IsMulCommutative ((P : Subgroup G) ⊓ J : Subgroup G) ∧
  (∃ Z : Subgroup G, IsCyclic Z ∧ x ∈ Z ∧
    (∀ t ∈ (P : Subgroup G) ⊓ J, ∀ c ∈ Z, t * c = c * t) ∧
    ((P : Subgroup G) ⊓ J) ⊓ Z = ⊥ ∧
    (P : Subgroup G) = ((P : Subgroup G) ⊓ J) ⊔ Z) ∧
  LineWeaklyClosed x (P : Subgroup G)

@[expose] def u3VPlane {G : Type} [Group G] (P : Subgroup G) (J : Subgroup G) (x : G) :
    Subgroup G :=
  ((center ↥(P ⊓ J)).map (P ⊓ J).subtype) ⊔ zpowers x

@[expose] def U3PointLemma43 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M J : Subgroup G) (x : G) : Prop :=
  ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → u3VPlane (P : Subgroup G) J x ≤ normalizer (Y : Set G) →
    IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) → normalizer (Y : Set G) ≤ M

@[expose] def GenericU3At (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Subgroup G → Prop) : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → IsRankThreeU3 Q → Φ p P M x J

end CFSG.LocalAnalysis.RankThreeTheoremC
