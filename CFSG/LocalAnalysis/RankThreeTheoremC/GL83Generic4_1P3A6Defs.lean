module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped MatrixGroups

@[expose] def IsRankThreeA6 (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* PSL(2, GaloisField 3 2))

structure IsA6Normal {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (J : Subgroup G) : Prop where
  le_centralizer : J ≤ centralizer ({x} : Set G)
  centralizer_le : centralizer ({x} : Set G) ≤ normalizer (J : Set G)
  perfect : Group.IsPerfect J
  not_le : ¬ J ≤ M
  lt_core : rankThreePrimeCore 3 J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore 3 J ≤ N →
    N = rankThreePrimeCore 3 J ∨ N = J
  iso : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore 3 J).subgroupOf J ∧ IsRankThreeA6 Q

@[expose] def A6Prop34 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) : Prop :=
  IsMulCommutative ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) ∧
  (∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ p = 1 →
    y ∈ ((P : Subgroup G) ⊓ J) ⊔ zpowers x) ∧
  (∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
      (zpowers x).map (MulAut.conj g).toMonoidHom ≤ J)

@[expose] def A6InV (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G) (J : Subgroup G)
    (x : G) (U : Subgroup G) : Prop :=
  U ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧ IsElemAbelian p U ∧ Nat.card U = p ^ 2 ∧
  x ∈ U ∧ ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≠ U ⊓ J

@[expose] def A6PointLemma42 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M J : Subgroup G) (x : G) : Prop :=
  ∀ U : Subgroup G, A6InV p P J x U → ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M

@[expose] def A6PointLemma43 (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M J : Subgroup G) (x : G) : Prop :=
  ∃ U : Subgroup G, A6InV p P J x U ∧
    ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) → normalizer (Y : Set G) ≤ M

@[expose] def GenericA6At (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Subgroup G → Prop) : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → IsRankThreeA6 Q → Φ p P M x J

end CFSG.LocalAnalysis.RankThreeTheoremC
