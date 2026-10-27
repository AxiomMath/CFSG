module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

structure Sp48NInSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ K A₀ V₀ : Subgroup Y) : Prop where
  card_T : Nat.card T = 3 ^ 5
  center_pow : ∀ z ∈ centerOf T, z ^ 3 = 1
  card_center : Nat.card (centerOf T) = 3 ^ 2
  card_TK : Nat.card (T ⊓ K : Subgroup Y) = 3 ^ 4
  A_le : A₀ ≤ T
  A_pow : ∀ a ∈ A₀, a ^ 3 = 1
  A_comm : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a
  card_A : Nat.card A₀ = 3 ^ 3
  center_le_A : centerOf T ≤ A₀
  homocyclic : ∃ u v : Y, u ∈ T ⊓ K ∧ v ∈ T ⊓ K ∧ orderOf u = 9 ∧ orderOf v = 9 ∧
    u * v = v * u ∧ Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥
  orbit_nine : ∀ a ∈ A₀, a ∉ centerOf T → ∀ W : Fin 3 → Subgroup Y,
    ∃ u ∈ T ⊓ K, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i
  V_le : V₀ ≤ Y₀
  V_le_K : V₀ ≤ K
  V_perfect : ⁅V₀, V₀⁆ = V₀
  V_normal : Y₀ ≤ Subgroup.normalizer (V₀ : Set Y)
  TK_le_V : T ⊓ K ≤ V₀
  minimal : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → W = ⊥ ∨ V₀ ≤ W
  V_centralizer : Y₀ ⊓ Subgroup.centralizer (V₀ : Set Y) = ⊥
  sylow_normal : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → V₀ ≤ W →
    T ⊓ W = T ⊓ K ∨ T ⊓ W = T
  factors : ∃ V₁ V₂ : Subgroup Y, V₁ ⊔ V₂ = V₀ ∧ ⁅V₁, V₂⁆ = ⊥ ∧ ⁅V₁, V₁⁆ = V₁ ∧
    ⁅V₂, V₂⁆ = V₂ ∧
    (∃ d : TauCeti.ValidLieTypeIndex, IsCaseTwoIndex 3 d ∧ Nonempty (V₁ ≃* CatGroup d)) ∧
    (∃ d : TauCeti.ValidLieTypeIndex, IsCaseTwoIndex 3 d ∧ Nonempty (V₂ ≃* CatGroup d)) ∧
    T ≤ Subgroup.normalizer (V₁ : Set Y) ∧ T ≤ Subgroup.normalizer (V₂ : Set Y) ∧
    ∃ τ ∈ Y₀, V₁.map (MulAut.conj τ).toMonoidHom = V₂ ∧
      V₂.map (MulAut.conj τ).toMonoidHom = V₁

@[expose] def KFactSp48NonsolvLocal : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsSpFourEightIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 3 (T : Subgroup Y) → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      ¬ Group.IsSolvable Y₀ → ∃ A₀ V₀ : Subgroup Y, Sp48NInSitu (T : Subgroup Y) Y₀ K A₀ V₀

section Package

variable {G : Type} [Group G] [Finite G]

@[expose] def Sp48NPiece (K N V : Subgroup G) : Prop :=
  ⁅V, V⁆ = V ∧ V ≤ K ∧ ¬ V ≤ N ∧ K ≤ Subgroup.normalizer ((V ⊔ N : Subgroup G) : Set G) ∧
    (∀ W : Subgroup G, W ≤ K → K ≤ Subgroup.normalizer (W : Set G) → W ≤ N ∨ V ≤ W ⊔ N) ∧
    ∀ g ∈ K, (∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ N) → g ∈ N

@[expose] def Sp48NFactors (K N R V : Subgroup G) : Prop :=
  ∃ V₁ V₂ : Subgroup G, V₁ ≤ V ∧ V₂ ≤ V ∧ ⁅V₁, V₁⁆ = V₁ ∧ ⁅V₂, V₂⁆ = V₂ ∧ ⁅V₁, V₂⁆ ≤ N ∧
    V ≤ V₁ ⊔ V₂ ⊔ N ∧
    (∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V₁ →* CatGroup d), IsCaseTwoIndex 3 d ∧
      Function.Surjective ψ ∧ ∀ x : V₁, ψ x = 1 → (x : G) ∈ N) ∧
    (∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V₂ →* CatGroup d), IsCaseTwoIndex 3 d ∧
      Function.Surjective ψ ∧ ∀ x : V₂, ψ x = 1 → (x : G) ∈ N) ∧
    R ≤ Subgroup.normalizer ((V₁ ⊔ N : Subgroup G) : Set G) ∧
    R ≤ Subgroup.normalizer ((V₂ ⊔ N : Subgroup G) : Set G) ∧
    ∃ τ ∈ K, V₁.map (MulAut.conj τ).toMonoidHom ≤ V₂ ⊔ N ∧
      V₂.map (MulAut.conj τ).toMonoidHom ≤ V₁ ⊔ N

structure D1Sp48NData (P : Sylow 3 G) (M H R X U A V : Subgroup G) : Prop where
  surv : D1SurvivorData 3 P M H R X
  center_le : centerOf R ≤ X
  card_R : Nat.card R = 3 ^ 5
  elem_X : IsElemAbelian 3 X
  card_X : Nat.card X = 3 ^ 2
  U_le : U ≤ R
  card_U : Nat.card U = 3 ^ 4
  A_le : A ≤ R
  elem_A : IsElemAbelian 3 A
  card_A : Nat.card A = 3 ^ 3
  X_le_A : X ≤ A
  X_le_U : X ≤ U
  homocyclic : ∃ u v : G, u ∈ U ∧ v ∈ U ∧ orderOf u = 9 ∧ orderOf v = 9 ∧ u * v = v * u ∧
    Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥
  orbit_nine : ∀ a ∈ A, a ∉ X → ∀ W : Fin 3 → Subgroup G,
    ∃ u ∈ U, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i
  piece : Sp48NPiece (H ⊓ M) (GLBPrimeCore 3 H) V
  U_le_V : U ≤ V ⊔ GLBPrimeCore 3 H
  sylow_normal : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    ¬ Y ≤ GLBPrimeCore 3 H → R ⊓ Y = U ∨ R ⊓ Y = R
  factors : Sp48NFactors (H ⊓ M) (GLBPrimeCore 3 H) R V

end Package

@[expose] def StmtSp48NData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpFourEightIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) →
    ¬ Group.IsSolvable (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∃ A V : Subgroup G, D1Sp48NData P M H R (centerOf R) (d1LiftX 3 H R K) A V

end CFSG.AGLEmbedding
