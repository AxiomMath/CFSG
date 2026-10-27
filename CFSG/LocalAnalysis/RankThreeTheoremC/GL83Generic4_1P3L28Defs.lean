module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def IsRankThreeL28 (K : Type) [Group K] : Prop :=
  IsoLie K (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)

structure IsL28Normal {G : Type} [Group G] [Finite G] (M : Subgroup G) (x : G)
    (J : Subgroup G) : Prop where
  le_centralizer : J ≤ centralizer ({x} : Set G)
  centralizer_le : centralizer ({x} : Set G) ≤ normalizer (J : Set G)
  perfect : Group.IsPerfect J
  not_le : ¬ J ≤ M
  lt_core : rankThreePrimeCore 3 J < J
  minimal : ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore 3 J ≤ N →
    N = rankThreePrimeCore 3 J ∨ N = J
  iso : ∃ (Q : Type) (_ : Group Q) (ψ : ↥J →* Q), Function.Surjective ψ ∧
    ψ.ker = (rankThreePrimeCore 3 J).subgroupOf J ∧ IsRankThreeL28 Q

@[expose] def GenericL28At (G : Type) [Group G] [Finite G]
    (Φ : ∀ p : ℕ, Sylow p G → Subgroup G → G → Subgroup G → Prop) : Prop :=
  GenericAt G fun p P M x => p = 3 → ∀ J : Subgroup G,
    J ≤ Subgroup.centralizer ({x} : Set G) →
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) → Group.IsPerfect J →
    rankThreePrimeCore p J < J →
    (∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → rankThreePrimeCore p J ≤ N →
      N = rankThreePrimeCore p J ∨ N = J) → ¬ J ≤ M →
    ∀ (Q : Type) [Group Q] (ψ : ↥J →* Q), Function.Surjective ψ →
      ψ.ker = (rankThreePrimeCore p J).subgroupOf J → IsRankThreeL28 Q → Φ p P M x J

end CFSG.LocalAnalysis.RankThreeTheoremC
