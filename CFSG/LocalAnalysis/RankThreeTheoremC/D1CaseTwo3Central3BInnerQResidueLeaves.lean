module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.RankThreeCoreUniqueness.Helpers
   Subgroup

@[expose] def KFactKFC1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Sylow 3 X) (X₀ : Subgroup X) (x : X),
    CatalogSimpleSections X → ReducedNongeneration 3 X T X₀ →
    Open.pRank 3 (T : Subgroup X) = 3 → x ∈ center X → orderOf x = 3 →
    (∀ D : Subgroup X, D ≤ X₀ → IsPGroup 3 D → ¬ IsCyclic (D ⊔ zpowers x : Subgroup X) →
      normalizer (D : Set X) ≤ X₀) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      (X₀ ≤ normalizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
        K ⊓ normalizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀) ∧
      (∀ D : Subgroup X, D ≤ (T : Subgroup X) ⊓ K →
        K ⊓ normalizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ normalizer (D : Set X) →
        D ≤ (frattini ↥((T : Subgroup X) ⊓ K)).map ((T : Subgroup X) ⊓ K).subtype ∨
          D = (T : Subgroup X) ⊓ K) ∧
      (∃ Q : Subgroup X, Q ≤ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
        centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ normalizer (Q : Set X) ∧
        Nat.Coprime 3 (Nat.card Q) ∧
        ∀ g ∈ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X), ∃ n : ℕ, g ^ 3 ^ n ∈ Q) ∧
      (∀ y ∈ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X), IsPGroup 3 (zpowers y) →
        ∃ k ∈ K ⊓ centralizer (((T : Subgroup X) ⊓ K : Subgroup X) : Set X),
          y * k⁻¹ ∈ centralizer (K : Set X)) ∧
      (IsCyclic (centralizer (K : Set X)) ∧ IsPGroup 3 (centralizer (K : Set X))) ∧
      K.Normal

@[expose] def KFactCaseTwoFieldInvertThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsCaseTwoGroup 3 K → ∀ φ : MulAut K, φ ^ 3 = 1 →
    (¬ ∃ y : K, φ = MulAut.conj y) → ∀ t : K, orderOf t = 3 → φ t = t →
      ∃ s : K, s ^ 2 = 1 ∧ φ s = s ∧ s * t * s⁻¹ = t⁻¹

end CFSG.LocalAnalysis.RankThreeTheoremC
