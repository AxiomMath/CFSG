module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsReeFFourFiveIndex (d : TauCeti.ValidLieTypeIndex) : Prop := d.1 = .reeF4 2

structure ReeF4InSitu {Y : Type} [Group Y] [Finite Y] (T Y₀ : Subgroup Y) : Prop where
  le_normalizer : Y₀ ≤ Subgroup.normalizer (T : Set Y)
  primeCore : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    Nat.Coprime 5 (Nat.card W) → W = ⊥
  normal_dichotomy : ∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
    W = ⊥ ∨ centerOf T ≤ W
  centralizer_le : Y₀ ⊓ Subgroup.centralizer (centerOf T : Set Y) ≤ T
  solvable : Group.IsSolvable Y₀
  center_elem : IsElemAbelian 5 (centerOf T)
  center_card : Nat.card (centerOf T) = 5 ^ 2
  transitive : ∀ F F' : Subgroup Y, F ≤ centerOf T → F' ≤ centerOf T → Nat.card F = 5 →
    Nat.card F' = 5 → ∃ g ∈ Y₀, F.map (MulAut.conj g).toMonoidHom = F'
  irred : ∀ Y₁ : Subgroup Y, Y₁ ≤ Y₀ → Y₁.relIndex Y₀ ≤ 3 → ∀ F : Subgroup Y,
    F ≤ centerOf T → Y₁ ≤ Subgroup.normalizer (F : Set Y) → F = ⊥ ∨ F = centerOf T

@[expose] def KFactReeF4Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsReeFFourFiveIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 5 Y) (Y₀ : Subgroup Y),
      3 ≤ Open.pRank 5 (T : Subgroup Y) → GLBWeakCore 5 (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ →
      ReeF4InSitu (T : Subgroup Y) Y₀ ∧ centerOf (T : Subgroup Y) ≤ K

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ReeF4

variable {G : Type} [Group G] [Finite G]

structure D1ReeF4Data (P : Sylow 5 G) (M H R X : Subgroup G) : Prop where
  surv : D1SurvivorData 5 P M H R X
  elem : IsElemAbelian 5 X
  card_X : Nat.card X = 5 ^ 2
  perfect_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Y ≤ GLBPrimeCore 5 H
  normalizer_le : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (X : Set G)
  transitive : ∀ F F' : Subgroup G, F ≤ X → F' ≤ X → Nat.card F = 5 → Nat.card F' = 5 →
    ∃ g ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G), F.map (MulAut.conj g).toMonoidHom = F'
  irred : ∀ Y₁ : Subgroup G, Y₁ ≤ H ⊓ M ⊓ Subgroup.normalizer (R : Set G) →
    Y₁.relIndex (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) ≤ 3 → ∀ F : Subgroup G, F ≤ X →
      Y₁ ≤ Subgroup.normalizer (F : Set G) → F = ⊥ ∨ F = X

end ReeF4

@[expose] def StmtReeF4Data : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 5)] {d : TauCeti.ValidLieTypeIndex},
    IsReeFFourFiveIndex d → ∀ {T : Type} [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    ∀ {P : Sylow 5 G} {M H R U : Subgroup G}, D1SocleConfig T 5 P M H R U →
      D1ReeF4Data P M H R (centerOf R) ∧ centerOf R ≤ U

@[expose] def StmtReeF4MSide : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R X : Subgroup G},
    D1ReeF4Data P M H R X → (∀ q ∈ GLBBetaFour G, q < 5 → D1At G q) →
    CFSG.pCore 5 (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

end CFSG.AGLEmbedding
