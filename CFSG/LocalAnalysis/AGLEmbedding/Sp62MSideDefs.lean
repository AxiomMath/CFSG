module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Sp62

variable {G : Type} [Group G] [Finite G]

@[expose] def U42Piece (K N : Subgroup G) (V : Subgroup G) : Prop :=
  ⁅V, V⁆ = V ∧ V ≤ K ∧ ¬ V ≤ N ∧ K ≤ Subgroup.normalizer ((V ⊔ N : Subgroup G) : Set G) ∧
    (V ⊔ N).relIndex K ≤ 2 ∧
    (∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V →* CatGroup d), IsUFourTwoIndex d ∧
      Function.Surjective ψ ∧ Nat.Coprime 3 (Nat.card ψ.ker)) ∧
    (∀ W : Subgroup G, W ≤ K → V ≤ Subgroup.normalizer (W : Set G) → V ≤ W ⊔ N ∨ ⁅W, V⁆ ≤ N) ∧
    ∀ g ∈ K, (∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ N) → g ∈ N

structure D1Sp62Data (P : Sylow 3 G) (M H R V : Subgroup G) : Prop where
  surv : D1SurvivorData 3 P M H R R
  card_R : Nat.card R = 3 ^ 4
  piece : U42Piece (H ⊓ M) (GLBPrimeCore 3 H) V
  dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore 3 H ∨ V ≤ Y

end Sp62

@[expose] def StmtSp62Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ¬ HasKlingenData 3 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsSpSixTwoIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) → ∃ V : Subgroup G, D1Sp62Data P M H R V

end CFSG.AGLEmbedding
