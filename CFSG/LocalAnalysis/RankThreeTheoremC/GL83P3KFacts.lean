module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open

@[expose] def KFactWeakClosureOmega3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    3 ∣ Nat.card K → ∀ Q : Sylow 3 X, K ⊔ (Q : Subgroup X) = ⊤ →
      (∃ E : Subgroup X, E ≤ (Q : Subgroup X) ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
        ∀ y ∈ (Q : Subgroup X), y ^ 3 = 1 → y ∈ E) →
      ∀ A : Subgroup X, A ≤ (Q : Subgroup X) → Nat.card A = 3 →
        ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) ∧
          A.map (MulAut.conj g).toMonoidHom ≠ A

@[expose] def KFactCentralOmega : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → 3 ∣ Nat.card (Subgroup.center K) →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) < 4 →
      ∀ S : Sylow 3 K, ¬ ∀ a ∈ (S : Subgroup K), ∀ b ∈ (S : Subgroup K),
        a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a

@[expose] def KFactWeakClosureHeisThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → Subgroup.centralizer (K : Set X) = ⊥ →
    3 ∣ Nat.card K → ∀ Q : Sylow 3 X, K ⊔ (Q : Subgroup X) = ⊤ →
      ∀ Q₀ Q₁ : Subgroup X, IsCyclic Q₀ → Q₀ ≠ ⊥ → Nat.card Q₁ = 3 ^ 3 →
        ¬ IsMulCommutative Q₁ → (∀ q ∈ Q₁, q ^ 3 = 1) → (∀ a ∈ Q₀, ∀ b ∈ Q₁, a * b = b * a) →
        Q₀ ⊓ Q₁ = ⊥ → Q₀ ⊔ Q₁ = (Q : Subgroup X) →
        ∀ A : Subgroup X, A ≤ (Q : Subgroup X) → Nat.card A = 3 →
          ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) ∧
            A.map (MulAut.conj g).toMonoidHom ≠ A

end CFSG.LocalAnalysis.RankThreeTheoremC
