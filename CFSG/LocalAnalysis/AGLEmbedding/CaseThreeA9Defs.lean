module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure A9InSitu {Y : Type} [Group Y] [Finite Y] (T B Y₀ : Subgroup Y) : Prop where
  le_normalizer : Y₀ ≤ Subgroup.normalizer (B : Set Y)
  primeCore : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    Nat.Coprime 3 (Nat.card W) → W = ⊥
  normal_dichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ B ≤ W
  centralizer_le : Y₀ ⊓ Subgroup.centralizer (B : Set Y) ≤ B
  pcore_le : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    IsPGroup 3 W → W ≤ B
  solvable : Group.IsSolvable Y₀
  pRank_le : Open.pRank 3 (⊤ : Subgroup Y) ≤ 3

@[expose] def KFactA9Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    Nonempty (K ≃* alternatingGroup (Fin 9)) → Subgroup.centralizer (K : Set Y) = ⊥ →
    ∀ (T : Sylow 3 Y) (B Y₀ : Subgroup Y), B ≤ T → IsElemAbelian 3 B → Nat.card B = 3 ^ 3 →
      GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A9InSitu (T : Subgroup Y) B Y₀

theorem kFactA3pLocal_three_of (hL : KFactA9Local) : @KFactA3pLocal 3 ⟨Nat.prime_three⟩ := by
  intro Y _ _ K hK e hC T B Y₀ hBT hB hBc hW hY₀
  have h := hL Y K hK e hC T B Y₀ hBT hB hBc hW hY₀
  exact ⟨h.primeCore, h.normal_dichotomy, h.centralizer_le.trans hBT⟩

section A9

variable {G : Type} [Group G] [Finite G]

structure D1A9DataCore (P : Sylow 3 G) (M H R X : Subgroup G) (σ z : G) : Prop where
  surv : D1SurvivorData 3 P M H R X
  elem : IsElemAbelian 3 X
  card_X : Nat.card X = 3 ^ 3
  card_R : Nat.card R = 3 ^ 4
  normalizer_le : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (X : Set G)
  pRank_le : Open.pRank 3 (H ⊓ M) ≤ 3
  perfect_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Y ≤ GLBPrimeCore 3 H
  pcore_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ 3 ^ k ∈ GLBPrimeCore 3 H) → Y ≤ X ⊔ GLBPrimeCore 3 H
  z_mem : z ∈ X
  z_ne : z ≠ 1
  z_center : z ∈ Subgroup.centralizer (R : Set G)
  center_le : centerOf R ≤ Subgroup.zpowers z
  σ_mem : σ ∈ R
  σ_not_mem : σ ∉ X
  σ_pow : σ ^ 3 = 1
  fix : ∀ x ∈ X, σ * x * σ⁻¹ = x → x ∈ Subgroup.zpowers z
  escape : ¬ Subgroup.normalizer ((Subgroup.closure {σ, z} : Subgroup G) : Set G) ≤ M

structure D1A9Data (P : Sylow 3 G) (M H R X : Subgroup G) (σ z : G) : Prop
    extends D1A9DataCore P M H R X σ z where
  four_le : 4 ≤ Open.pRank 3 (P : Subgroup G)

end A9

@[expose] def StmtA9Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G)
    (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)),
    D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9)) →
    ∃ (X : Subgroup G) (σ z : G), D1A9Data P M H R X σ z

@[expose] def StmtA9MSide : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R X : Subgroup G} {σ z : G},
    D1A9Data P M H R X σ z → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

end CFSG.AGLEmbedding
