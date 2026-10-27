module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section J3

variable {G : Type} [Group G] [Finite G]

structure J3SylowFacts (J : Type) [Group J] (T : Subgroup J) : Prop where
  maximal : ∀ Y₀ : Subgroup J, Subgroup.normalizer (T : Set J) ≤ Y₀ →
    Y₀ = Subgroup.normalizer (T : Set J) ∨ Y₀ = ⊤
  centralizer_center : Subgroup.centralizer (centerOf T : Set J) ≤ T
  center_irreducible : ∀ W : Subgroup J, W ≤ centerOf T →
    Subgroup.normalizer (T : Set J) ≤ Subgroup.normalizer (W : Set J) → W = ⊥ ∨ W = centerOf T
  center_elem : IsElemAbelian 3 (centerOf T) ∧ Nat.card (centerOf T) = 9
  nonabelian : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a
  singer : ∃ s ∈ Subgroup.normalizer (T : Set J), IsPGroup 2 (Subgroup.zpowers s) ∧
    ∀ W : Subgroup J, W ≤ T → W.relIndex T = 3 → s ^ 2 ∉ Subgroup.normalizer (W : Set J)
  two_top : ∀ y ∈ Subgroup.normalizer (T : Set J), ∃ e : ℕ, y ^ 2 ^ e ∈ T

@[expose] def KFactJ3Sylow : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    ∀ T : Sylow 3 J, J3SylowFacts J T

@[expose] def KFactJ3OuterInvolution : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    ∀ α : MulAut J, α ^ 2 = 1 → α ∉ (MulAut.conj : J →* MulAut J).range →
      ∀ E : Subgroup J, IsElemAbelian 3 E → Nat.card E = 9 → ∃ x ∈ E, α x ≠ x

@[expose] def KFactJ3OuterRank : Prop :=
  ∀ (J : Type) [Group J] [Finite J], Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ≤ 2 ∧
      Open.pRank 3 (⊤ : Subgroup J) = 3

structure J3InSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ : Subgroup Y) : Prop where
  le_normalizer : Y₀ ≤ Subgroup.normalizer (T : Set Y)
  centralizer_center : Subgroup.centralizer (centerOf T : Set Y) ≤ T
  center_irreducible : ∀ W : Subgroup Y, W ≤ centerOf T → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ W = centerOf T
  nonabelian : ∃ a ∈ T, ∃ b ∈ T, a * b ≠ b * a
  pRank_le : Open.pRank 3 (⊤ : Subgroup Y) ≤ 3
  singer : ∃ s ∈ Y₀ ⊓ Subgroup.normalizer (T : Set Y), IsPGroup 2 (Subgroup.zpowers s) ∧
    ∀ W : Subgroup Y, W ≤ T → W.relIndex T = 3 → s ^ 2 ∉ Subgroup.normalizer (W : Set Y)
  two_top : ∀ y ∈ Y₀, ∃ e : ℕ, y ^ 2 ^ e ∈ T

structure D1J3Config (P : Sylow 3 G) (M H R : Subgroup G) : Prop where
  ext : D1Extremal 3 P M H R
  glob : CFSG.AGLEmbeddingD2.AGLGlobal G
  socle : ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), K.Normal ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) ∧
    Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)) = ⊥

theorem D1ComponentConfig.d1J3Config [Fact (Nat.Prime 3)] {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hcfg : D1ComponentConfig 3 P M H R Rbar)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hK : IsComponentOf K ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K)
    (hcent : ∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype)
    (hZ : Subgroup.center K = ⊥)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    D1J3Config P M H R := by
  obtain ⟨e⟩ := e
  exact ⟨hcfg.ext, hcfg.glob.toAGLGlobal, K, normal_of_forall_isComponentOf_eq hK huniq,
    ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e⟩,
    hcfg.centralizer_eq_bot hK huniq hcent hZ⟩

structure D1J3Data (P : Sylow 3 G) (M H R : Subgroup G) : Prop where
  surv : D1SurvivorData 3 P M H R (centerOf R)
  pRank_le : Open.pRank 3 (H ⊓ M) ≤ 3
  nonabelian : ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a
  singer : ∃ s ∈ H ⊓ M, s ∈ Subgroup.normalizer (R : Set G) ∧ IsPGroup 2 (Subgroup.zpowers s) ∧
    ∀ W : Subgroup G, W ≤ R → W.relIndex R = 3 → s ^ 2 ∉ Subgroup.normalizer (W : Set G)
  normal_sup : H ⊓ M ≤ Subgroup.normalizer ((R ⊔ GLBPrimeCore 3 H : Subgroup G) : Set G)
  two_top : ∀ k ∈ H ⊓ M, ∃ e : ℕ, k ^ 2 ^ e ∈ R ⊔ GLBPrimeCore 3 H

@[expose] def StmtJ3Data : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G},
    D1J3Config P M H R → D1J3Data P M H R

end J3

@[expose] def StmtJ3Target : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    JStarTarget 3 (3 ^ 5) L

@[expose] def StmtJ3TargetCard : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    JStarTargetCard 3 5 (3 ^ 5) L

@[expose] def KFactJStarElimJ3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    JStarElimOf 3 (3 ^ 5) L

end CFSG.AGLEmbedding
