module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsSpFourEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q

@[expose] def StmtSp48Surv : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 3)] {d : TauCeti.ValidLieTypeIndex},
    IsSpFourEightIndex d → ∀ {T : Type} [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    ∀ {P : Sylow 3 G} {M H R U : Subgroup G}, D1SocleConfig T 3 P M H R U →
      D1SurvivorData 3 P M H R (centerOf R) ∧ centerOf R ≤ U

section Sp48

variable {G : Type} [Group G] [Finite G]

structure D1Sp48Data (P : Sylow 3 G) (M H R X U A : Subgroup G) : Prop where
  surv : D1SurvivorData 3 P M H R X
  card_R : Nat.card R = 3 ^ 5
  elem_X : IsElemAbelian 3 X
  card_X : Nat.card X = 3 ^ 2
  perfect_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Y ≤ GLBPrimeCore 3 H
  U_le : U ≤ R
  card_U : Nat.card U = 3 ^ 4
  A_le : A ≤ R
  elem_A : IsElemAbelian 3 A
  card_A : Nat.card A = 3 ^ 3
  X_le_A : X ≤ A
  X_le_U : X ≤ U
  sylow_normal : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    X ≤ Y → R ⊓ Y = X ∨ R ⊓ Y = A ∨ R ⊓ Y = U ∨ R ⊓ Y = R
  homocyclic : ∃ u v : G, u ∈ U ∧ v ∈ U ∧ orderOf u = 9 ∧ orderOf v = 9 ∧ u * v = v * u ∧
    Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥
  orbit_nine : ∀ a ∈ A, a ∉ X → ∀ W : Fin 3 → Subgroup G,
    ∃ u ∈ U, ∀ i, (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom ≠ W i

end Sp48

@[expose] def StmtSp48Target : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), IsSpFourEightIndex d → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* CatGroup d) → JStarTargetTwo 3 (3 ^ 5) L ∧ JStarTargetCard 3 4 (3 ^ 5) L

@[expose] def KFactJStarElimSp48 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), IsSpFourEightIndex d → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* CatGroup d) → JStarElimOf 3 (3 ^ 5) L

end CFSG.AGLEmbedding
