module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeAThreeP
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure A15InSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ : Subgroup Y) : Prop where
  primeCore : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    Nat.Coprime 5 (Nat.card W) → W = ⊥
  normal_dichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ T ≤ W
  centralizer_le : Y₀ ⊓ Subgroup.centralizer (T : Set Y) ≤ T
  pcore : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → IsPGroup 5 W →
    W = ⊥
  section_card : ∀ U : Subgroup Y, U ≤ Y₀ → ∀ (V : Subgroup U) [V.Normal],
    IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60
  normal_closure : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → T ≤ W →
    ∃ J : Fin 3 → Subgroup Y, (∀ i, J i ≤ W ∧ Nonempty (J i ≃* alternatingGroup (Fin 5))) ∧
      (∀ i j, i ≠ j → ⁅J i, J j⁆ = ⊥) ∧ T ≤ ⨆ i, J i

@[expose] def KFactA15Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    Nonempty (K ≃* alternatingGroup (Fin 15)) → Subgroup.centralizer (K : Set Y) = ⊥ →
    ∀ (T : Sylow 5 Y) (Y₀ : Subgroup Y), GLBWeakCore 5 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      A15InSitu (T : Subgroup Y) Y₀

section A15

variable {G : Type} [Group G] [Finite G]

structure D1A15Data (P : Sylow 5 G) (M H R : Subgroup G) (c : Fin 3 → G) (σ τ : G) : Prop where
  surv : D1SurvivorData 5 P M H R R
  ind : ∀ q ∈ GLBBetaFour G, q < 5 → D1At G q
  elem : IsElemAbelian 5 R
  card_R : Nat.card R = 5 ^ 3
  pcore : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ 5 ^ k ∈ GLBPrimeCore 5 H) → Y ≤ GLBPrimeCore 5 H
  c_mem : ∀ i, c i ∈ R
  closure_eq : Subgroup.closure (Set.range c) = R
  σ_mem : σ ∈ H ⊓ M
  σ_conj : ∀ i, σ * c i * σ⁻¹ = c (i + 1)
  τ_mem : τ ∈ H ⊓ M
  τ_conj : τ * c 0 * τ⁻¹ = c 0 ^ 2 ∧ τ * c 1 * τ⁻¹ = c 1 ∧ τ * c 2 * τ⁻¹ = c 2 ^ 2
  section_card : ∀ L : Subgroup G, L ≤ H ⊓ M → ∀ (V : Subgroup L) [V.Normal],
    (GLBPrimeCore 5 H).subgroupOf L ≤ V → IsSimpleGroup (L ⧸ V) →
    (∃ a b : L ⧸ V, a * b ≠ b * a) → Nat.card (L ⧸ V) = 60
  normal_closure : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    R ≤ Y → ∃ J : Fin 3 → Subgroup G, (∀ i, J i ≤ Y ∧ ⁅J i, J i⁆ = J i ∧
      ∃ φ : ↥(J i) →* alternatingGroup (Fin 5), Function.Surjective φ ∧
        ∀ x : ↥(J i), φ x = 1 ↔ (x : G) ∈ GLBPrimeCore 5 H) ∧
      (∀ i j, i ≠ j → ⁅J i, J j⁆ ≤ GLBPrimeCore 5 H) ∧ R ≤ ⨆ i, J i

end A15

@[expose] def StmtA15Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 5)] (P : Sylow 5 G)
    (M H R : Subgroup G) (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)),
    D1ComponentConfig 5 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 5)),
      orderOf c = 5 → c ∈ (Subgroup.center K).map K.subtype) →
    Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 15)) →
    ∃ (c : Fin 3 → G) (σ τ : G), D1A15Data P M H R c σ τ

@[expose] def StmtA15BlockOrbit : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
    {σ τ : G}, D1A15Data P M H R c σ τ → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      R ≤ blockClosure M (H ⊓ M) L → False

@[expose] def StmtA15NoBlockOrbit : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R : Subgroup G} {c : Fin 3 → G}
    {σ τ : G}, D1A15Data P M H R c σ τ →
      (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        (H ⊓ M) ⊓ blockClosure M (H ⊓ M) L ≤ GLBPrimeCore 5 H) → False

theorem d1CaseThreeA15_of (hData : StmtA15Data) (hA : StmtA15BlockOrbit)
    (hB : StmtA15NoBlockOrbit) : D1CaseThreeA15 := by
  intro G _ _ _ P M H R Rbar hcfg K hK huniq _ hcent _ hZ e
  obtain ⟨c, σ, τ, hD⟩ := hData G P M H R Rbar hcfg K hK huniq hcent hZ e
  refine hB hD fun L hL => ?_
  have hYn : H ⊓ M ≤ Subgroup.normalizer (((H ⊓ M) ⊓ blockClosure M (H ⊓ M) L : Subgroup G) :
      Set G) :=
    (le_inf Subgroup.le_normalizer (le_normalizer_blockClosure inf_le_right)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rcases hD.surv.normal_dichotomy _ inf_le_left hYn with hle | hRle
  · exact hle
  · exact (hA hD L hL (hRle.trans inf_le_right)).elim

end CFSG.AGLEmbedding
