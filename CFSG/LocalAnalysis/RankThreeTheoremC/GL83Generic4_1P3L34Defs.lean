module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open scoped MatrixGroups

@[expose] def IsRankThreeL34 (K : Type) [Group K] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ IsoLie K (.A 2 q)

@[expose] def KFactL34TwoSignalizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL34 K → ∀ (Q : Sylow 3 K),
    IsElemAbelian 3 (Q : Subgroup K) ∧
      ∀ u ∈ (Q : Subgroup K), orderOf u = 3 →
        ⊤ ≤ rankThreeGamma 1 3 (Q : Subgroup K) ⊔
          sSup {T : Subgroup K | IsPGroup 2 T ∧ u ∈ normalizer (T : Set K)}

@[expose] def KFactL34Three : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsRankThreeL34 K → ∀ (T : Sylow 3 K),
    Nat.card (T : Subgroup K) = 3 ^ 2 ∧ centralizer ((T : Subgroup K) : Set K) ≤ T ∧
    (∀ Y : Subgroup K, normalizer ((T : Subgroup K) : Set K) ≤ Y →
      Y = normalizer ((T : Subgroup K) : Set K) ∨ Y = ⊤) ∧
    ∀ u ∈ (T : Subgroup K), u ≠ 1 → ∀ V : Subgroup K, IsPGroup 2 V →
      V ≤ normalizer ((T : Subgroup K) : Set K) → u ∈ normalizer (V : Set K) → V = ⊥

@[expose] def KFactL34Unitary : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal →
    centralizer (K : Set X) = ⊥ → IsRankThreeL34 ↥K →
    ∀ T : Subgroup X, IsElemAbelian 3 T → Nat.card T = 3 ^ 2 → T ≤ K →
      Nat.card (rankThreePrimeCore 3 (rankThreeGamma 1 3 T)) ≤ 2 ∧
      ∀ β ∈ rankThreePrimeCore 3 (rankThreeGamma 1 3 T),
        (∀ t ∈ T, β * t = t * β) ∧
        (β ≠ 1 → ∀ S : Subgroup X, S ≤ K → IsSylowOf 2 S K → ∀ u ∈ T, orderOf u = 3 →
          u ∈ normalizer (S : Set X) → ∀ D : Subgroup X, D ≤ K →
            normalizer (S : Set X) ⊓ K ≤ D → β ∈ normalizer (D : Set X) → D = K)

structure IsL34Normal {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (J : Subgroup G) : Prop where
  le_centralizer : J ≤ centralizer ({x} : Set G)
  centralizer_le : centralizer ({x} : Set G) ≤ normalizer (J : Set G)
  perfect : Group.IsPerfect J
  not_le : ¬ J ≤ M
  lt_core : rankThreePrimeCore 3 J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore 3 J ≤ N →
    N = rankThreePrimeCore 3 J ∨ N = J
  iso : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore 3 J).subgroupOf J ∧ IsRankThreeL34 Q

@[expose] def L34Prop34 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  (P : Subgroup G) ≤ centralizer ({x} : Set G) ∧
  IsElemAbelian p (((P : Subgroup G) ⊓ J) ⊔ zpowers x) ∧
  Nat.card (((P : Subgroup G) ⊓ J) ⊔ zpowers x : Subgroup G) = p ^ 3 ∧
  (∀ y ∈ (P : Subgroup G), y ^ p = 1 → y ∈ ((P : Subgroup G) ⊓ J) ⊔ zpowers x) ∧
  LineWeaklyClosed x (P : Subgroup G)

@[expose] def L34PointLemma42 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M : Subgroup G) (x : G) : Prop :=
  ∀ U : Subgroup G, U ≤ (P : Subgroup G) → IsElemAbelian p U → Nat.card U = p ^ 2 → x ∈ U →
    ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M

@[expose] def L34PointLemma43 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M : Subgroup G) (x : G) : Prop :=
  ∃ U : Subgroup G, U ≤ (P : Subgroup G) ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧ x ∈ U ∧
    (∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) → normalizer (Y : Set G) ≤ M)

@[expose] def L34Remark (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (M J : Subgroup G) :
    Prop :=
  M ≤ normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore p M : Subgroup G) : Set G)

@[expose] def GenericL34At (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Subgroup G → Prop) : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → IsRankThreeL34 Q → Φ p P M x J

@[expose] def L34PlaneData (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M : Subgroup G) (x : G) (J : Subgroup G) : Prop :=
  L34Prop34 p P J x ∧ L34PointLemma42 p P M x ∧ L34PointLemma43 p P M x ∧ L34Remark p P M J

end CFSG.LocalAnalysis.RankThreeTheoremC
