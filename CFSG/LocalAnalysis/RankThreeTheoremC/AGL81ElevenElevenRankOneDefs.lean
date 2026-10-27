module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenCfgChain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactNineThreeListRankOne : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), NineThreeListGroup p ↥K →
    Open.pRank p K ≤ 1 → IsCaseTwoGroup p ↥K

@[expose] def KFactCaseTwoSylowAut : Prop :=
  ∀ (p : ℕ) (L : Type) [Group L] [Finite L], IsCaseTwoGroup p L →
    (∀ T : Sylow p L, Nat.card T = p ^ 2) ∧
      ∀ A : Subgroup (MulAut L), IsPGroup p A → Nat.card A ≤ p ^ 3

structure RankOneSylowData (p : ℕ) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (W : Subgroup G) (y z : G) : Prop where
  pgroup : IsPGroup p W
  le : W ≤ H ⊓ M
  max : ∀ W' : Subgroup G, IsPGroup p W' → W' ≤ H → W ≤ W' → W' = W
  z_mem : z ∈ W ⊓ d1PlusCore p H K
  z_order : orderOf z = p
  z_central : ∀ w ∈ W, w * z = z * w
  cyclic : IsCyclic ↥(W ⊓ d1PlusCore p H K)
  y_lift : d1LiftX p H W K = Subgroup.zpowers y
  y_Q : d1LiftX p H Q K = Subgroup.zpowers y
  y_order : orderOf y = p ^ 2
  y_X : Subgroup.zpowers y ⊓ d1PlusCore p H K = ⊥
  outer : ∃ a ∈ W, orderOf a = p ∧ a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K
  noncomm : ∀ a ∈ W, a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K → a * y ≠ y * a

variable (G) in
@[expose] def AGL81ElevenThreeDvdCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
      p ∣ Nat.card (jOne H L)

variable (G) in
@[expose] def AGL81ElevenElevenParabolicComm : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ∀ B : Subgroup G, B ≤ H ⊓ M → IsPGroup p B →
    (∀ b ∈ B, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
    ¬ 2 ∣ (jZero H L ⊔ pCoreOf 2 (H ⊓ L)).relIndex L →
      ⁅⁅B, B⁆, L⁆ ≤ pCoreOf 2 L

variable (G) in
@[expose] def AGL81ElevenElevenRankOneCent : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ¬ HasPrimeConstraint (G := H) p → IsCaseTwoGroup p ↥K →
    3 ≤ Open.pRank p H → d1PlusCore p H K ≤ M → K.Normal →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → (L.subgroupOf M).Normal →
    ¬ AGL81ElevenFiveOne p H K L → jZero H L ≤ d1PlusCore p H K →
    Open.pRank p (d1PlusCore p H K) = 1 → p ∣ Nat.card (jZero H L) →
    ∀ (W : Subgroup G) (y a z : G), IsPGroup p W → W ≤ H ⊓ M →
      (∀ W' : Subgroup G, IsPGroup p W' → W' ≤ H → W ≤ W' → W' = W) →
      z ∈ W ⊓ d1PlusCore p H K → orderOf z = p → (∀ w ∈ W, w * z = z * w) →
      z ∈ jZero H L → (¬ ∀ x ∈ jZero H L, z * x * z⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
      d1LiftX p H W K = Subgroup.zpowers y → orderOf y = p ^ 2 →
      (∀ w ∈ W, w ∉ hyp111Pre p H K ⊔ d1PlusCore p H K → w * y ≠ y * w) →
      a ∈ W → orderOf a = p → a ∉ hyp111Pre p H K ⊔ d1PlusCore p H K →
      (∀ b ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers a, ∀ x ∈ jZero H L,
        b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
      ⁅Subgroup.zpowers (y ^ p), L⁆ ≤ pCoreOf 2 L →
      Subgroup.centralizer ({y ^ p} : Set G) ≤ M →
      ∀ b ∈ Subgroup.zpowers (y ^ p) ⊔ Subgroup.zpowers a, b ∉ Subgroup.zpowers (y ^ p) →
        Subgroup.centralizer ({b} : Set G) ≤ M

end CFSG.LocalAnalysis.RankThreeTheoremC
