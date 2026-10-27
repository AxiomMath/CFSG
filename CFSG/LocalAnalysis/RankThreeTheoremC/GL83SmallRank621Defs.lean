module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Thompson

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

@[expose] def KFactLemma2813 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X K R P₁ : Subgroup A) (b : A),
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    K ≤ X → X ≤ normalizer (K : Set A) → ⁅K, K⁆ = K → X = K ⊔ pCoreOf 2 X →
    (∃ f : ↥K →* GL32, Function.Surjective f ∧ ∀ k : ↥K, f k = 1 ↔ (k : A) ∈ pCoreOf 2 X) →
    R ≤ X → IsPGroup 2 R → ¬ 2 ∣ (R.subgroupOf X).index →
    R ≤ P₁ → P₁ ≤ X → (P₁.subgroupOf X).index = 7 →
    (∀ Q₀ : Subgroup A, Q₀ ≤ pCoreOf 2 P₁ → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 P₁)).Characteristic →
      ¬ X ≤ (X ⊓ centralizer ((omegaCenter (pCoreOf 2 P₁) : Subgroup A) : Set A)) ⊔
        (X ⊓ normalizer (Q₀ : Set A))) →
    ∀ D : Subgroup A, D ≤ P₁ → IsPGroup 3 D → ¬ 3 ∣ (D.subgroupOf P₁).index →
      Nat.card ↥⁅omegaCenter (pCoreOf 2 P₁), D⁆ ≤ 16 ∧
      (X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) ≠ P₁ →
        ¬ X ≤ centralizer ((omegaCenter R : Subgroup A) : Set A) →
        ∀ v ∈ omegaCenter (pCoreOf 2 P₁), (∀ d ∈ D, v * d = d * v) →
          ∀ x ∈ X, v * x = x * v) ∧
      (X ≤ centralizer ((omegaCenter R : Subgroup A) : Set A) →
        b ∈ normalizer (X : Set A) → b ^ 3 = 1 → ⁅zpowers b, K⁆ ≤ pCoreOf 2 X →
        (∃ x ∈ X, b * x ≠ x * b) →
        ∀ B' : Subgroup A, B' ≤ X ⊔ zpowers b → IsPGroup 3 B' → D ≤ B' →
          ¬ 3 ∣ (B'.subgroupOf (X ⊔ zpowers b)).index →
          ∀ v ∈ omegaCenter (pCoreOf 2 P₁), (∀ d ∈ D, v * d = d * v) →
            ∀ y ∈ B', ∀ x ∈ X,
              (v * y * v⁻¹ * y⁻¹) * x = x * (v * y * v⁻¹ * y⁻¹))

end CFSG.LocalAnalysis.RankThreeTheoremC
