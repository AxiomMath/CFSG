module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsGTwoEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q

section G28

variable {G : Type} [Group G] [Finite G]

@[expose] def SU38Piece (K N : Subgroup G) (z : G) (V : Subgroup G) : Prop :=
  ⁅V, V⁆ = V ∧ V ≤ K ∧ ¬ V ≤ N ∧ K ≤ Subgroup.normalizer ((V ⊔ N : Subgroup G) : Set G) ∧
    (∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V →* CatGroup d), IsUThreeEightIndex d ∧
      Function.Surjective ψ) ∧
    (∀ W : Subgroup G, W ≤ K → V ≤ Subgroup.normalizer (W : Set G) → V ≤ W ⊔ N ∨ ⁅W, V⁆ ≤ N) ∧
    ∀ g ∈ K, (∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ N) → g ∈ Subgroup.zpowers z ⊔ N

structure D1G28Data (P : Sylow 3 G) (M H R : Subgroup G) (z : G) : Prop where
  ph3 : D1PhaseThree 3 P M H R
  z_mem : z ∈ R
  z_center : z ∈ Subgroup.centralizer (R : Set G)
  z_order : orderOf z = 3
  center_le : centerOf R ≤ Subgroup.zpowers z
  card_R : Nat.card R = 3 ^ 6
  dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore 3 H ∨ Y ≤ Subgroup.zpowers z ⊔ GLBPrimeCore 3 H ∨
      ∃ V : Subgroup G, V ≤ Y ∧ SU38Piece (H ⊓ M) (GLBPrimeCore 3 H) z V

end G28

@[expose] def StmtG28Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ∀ d : TauCeti.ValidLieTypeIndex, IsGTwoEightIndex d →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) → ∃ z : G, D1G28Data P M H R z

@[expose] def StmtG28MSide : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G} {z : G},
    D1G28Data P M H R z → False

theorem d1CaseThreeG28_of (hDat : StmtG28Data) (hM : StmtG28MSide) : D1CaseThreeG28 := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  obtain ⟨hp3, hd'⟩ := hd
  subst hp3
  obtain ⟨z, hz⟩ := hDat G P M H R Rbar hcfg K hK huniq hcent d hd' e
  exact hM hz

end CFSG.AGLEmbedding
