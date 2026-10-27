module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Shape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

@[expose] def KFactL28ThreeQuotient : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    3 ∣ Nat.card K → ∀ Q : Subgroup X, IsSylowOf 3 Q ⊤ → L28Shape 3 Q →
      ¬ Q ≤ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆

@[expose] def KFactOutThreeNilpotent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → CFSG.Open.pRank 3 K ≤ 1 →
    ∃ R : Subgroup Y, R ≤ normalizer (K : Set Y) ∧
      (∀ g ∈ normalizer (K : Set Y), ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
      K ⊔ Subgroup.centralizer (K : Set Y) ≤ R ∧
      (∀ d ∈ normalizer (K : Set Y), ∃ n : ℕ, d ^ 3 ^ n ∈ R) ∧
      ∀ d ∈ R, (∃ n : ℕ, d ^ 3 ^ n ∈ K ⊔ Subgroup.centralizer (K : Set Y)) →
        d ∈ K ⊔ Subgroup.centralizer (K : Set Y)

@[expose] def KFactOutThreeCoprime : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → (Nat.card K).factorization 3 = 1 →
    ∀ d ∈ normalizer (K : Set Y), (∃ n : ℕ, d ^ 3 ^ n = 1) →
      d ∈ K ⊔ Subgroup.centralizer (K : Set Y)

@[expose] def KFactSylowM27 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    ∀ Q : Subgroup X, IsSylowOf 3 Q ⊤ → Nat.card Q = 3 ^ 3 → ¬ IsMulCommutative Q →
      (∃ q ∈ Q, q ^ 3 ≠ 1) →
      ¬ Q ≤ K ∧ IsCyclic ↥(Q ⊓ K) ∧ Nat.card ↥(Q ⊓ K) = 3 ^ 2

@[expose] def KFactFieldGeneration : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ¬ IsRankThreeL28 K →
    ∀ T : Subgroup K, IsSylowOf 3 T ⊤ → IsCyclic T → Nat.card T = 3 ^ 2 →
    ∀ α : MulAut K, orderOf α = 3 → T.map α.toMonoidHom = T → (∃ t ∈ T, α t ≠ t) →
      T ⊔ α.toMonoidHom.eqLocus (MonoidHom.id K) = ⊤

end CFSG.LocalAnalysis.RankThreeTheoremC
