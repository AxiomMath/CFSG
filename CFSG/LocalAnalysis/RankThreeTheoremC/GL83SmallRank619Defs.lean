module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank618CaseDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

structure Data619 {G : Type} [Group G] [Finite G] (M B H S K : Subgroup G) (z : G)
    (f : ↥K →* GL32) : Prop where
  charTwo : IsCharTwoType G
  twoLocal : IsTwoLocal H
  eq_normalizer : H = normalizer (pCoreOf 2 H : Set G)
  B_le : B ≤ H
  maxInv : IsMaxTwoInvariantIn B H S
  core_le : pCoreOf 2 H ≤ S
  S_ne_bot : S ≠ ⊥
  norm_le : ∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S → S ⊔ B ≤ normalizer (S₀ : Set G) →
    normalizer (S₀ : Set G) ≤ M
  char_le : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
    normalizer (S₀ : Set G) ≤ M
  K_le : K ≤ H
  K_normal : H ≤ normalizer (K : Set G)
  K_not_le : ¬ K ≤ M
  K_simple : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → K ⊓ pCoreOf 2 H ≤ N →
    N = K ⊓ pCoreOf 2 H ∨ N = K
  f_surj : Function.Surjective f
  f_ker : ∀ k : ↥K, f k = 1 ↔ (k : G) ∈ pCoreOf 2 H
  z_mem_K : z ∈ K
  z_mem_B : z ∈ B
  z_order : orderOf z = 3

@[expose] def GL83SmallRankProp614Core21 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → Group.IsSolvable M →
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) →
    ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
      ∀ H S : Subgroup G, Prop614Extremal M (zpowers x ⊔ zpowers z) H S →
        ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H →
        H = normalizer (pCoreOf 2 H : Set G) →
        IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S →
        pCoreOf 2 H ≤ S →
        (∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
          S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) →
          normalizer (S₀ : Set G) ≤ M) →
        (∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
          normalizer (S₀ : Set G) ≤ M) →
        rankThreePrimeCore 3 H ≤ M →
        rankThreePrimeCore 3 H ≤ pCoreOf 2 H →
        (∃ (K : Subgroup G) (b : G), Prop614Component M H K x z ∧
          Prop614Layer P M H K x z b ∧
          S ≤ K ⊔ pCoreOf 2 H ∧ (pCoreOf 2 H).relIndex S = 4) → False

end CFSG.LocalAnalysis.RankThreeTheoremC
