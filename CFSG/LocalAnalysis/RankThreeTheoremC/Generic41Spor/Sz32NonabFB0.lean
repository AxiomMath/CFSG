module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactNoM125Sylow' : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    ∀ S : Sylow 5 K, ¬ (Nat.card (S : Subgroup K) = 125 ∧ ¬ IsMulCommutative (S : Subgroup K) ∧
      (∀ s ∈ (S : Subgroup K), s ^ 25 = 1) ∧ ∃ s ∈ (S : Subgroup K), s ^ 5 ≠ 1)

@[expose] def KFactI714Four' : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ Q : Sylow 5 X, ¬ (Q : Subgroup X) ≤ K → Nat.card (Q : Subgroup X) = 125 →
      ¬ IsMulCommutative (Q : Subgroup X) → (∀ q ∈ (Q : Subgroup X), q ^ 25 = 1) →
      (∃ q ∈ (Q : Subgroup X), q ^ 5 ≠ 1) →
      (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ), ℓ ≠ 5 ∧
        CFSG.Blueprint.LieModel ↥K t n ℓ f) ∧
      (Nat.card (((Q : Subgroup X) ⊓ K : Subgroup X)) = 25 ∧ IsCyclic (((Q : Subgroup X) ⊓ K : Subgroup X)))

structure NF5 {Y : Type} [Group Y] [Finite Y] (F Γ B R₀ : Subgroup Y) (x : Y) : Prop where
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections Y
  core : primeComplementCore (G := Y) 5 = ⊥
  sylow : CFSG.ABGLocalTools.IsSylowOf 5 F ⊤
  nonab : ¬ IsMulCommutative F
  card : Nat.card F = 125
  exp : ∀ f ∈ F, f ^ 25 = 1
  cen : ∀ z ∈ F, (∀ f ∈ F, f * z = z * f) ↔ z ∈ Subgroup.zpowers x
  hB : ∀ b, b ∈ B ↔ (b ∈ F ∧ b ^ 5 = 1)
  Belem : IsElemAbelian 5 B
  Bcard : Nat.card B = 5 ^ 2
  FΓ : F ≤ Γ
  hC : ∀ b ∈ B, b ∉ Subgroup.zpowers x → Subgroup.centralizer ({b} : Set Y) ≤ Γ
  R_ne : R₀ ≠ ⊥
  R_two : IsPGroup 2 R₀
  R_norm : B ≤ Subgroup.normalizer (R₀ : Set Y)

structure NF5Z {Y : Type} [Group Y] (F : Subgroup Y) (z : Y) : Prop where
  mem : z ∈ F
  order : orderOf z = 5
  central : ∀ f ∈ F, f * z = z * f
  gen : ∀ w ∈ F, (∀ f ∈ F, f * w = w * f) → w ∈ Subgroup.zpowers z

structure NF5Cfg {Y : Type} [Group Y] [Finite Y] (F Γ B R₀ : Subgroup Y) (x : Y) (L : Subgroup Y) (z : Y) :
    Prop where
  data : NF5 F Γ B R₀ x
  comp : IsComponentOf L ⊤
  uniq : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L
  zgen : NF5Z F z
  zL : z ∈ L
  cen : Subgroup.center ↥L = ⊥
  normal : L.Normal
  cent : Subgroup.centralizer (L : Set Y) = ⊥

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
