module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

@[expose] def KFactWeakClosureHeis : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
    K.Normal → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    Subgroup.centralizer (K : Set X) = ⊥ → p ∣ Nat.card K →
    ∀ Q : Sylow p X, K ⊔ (Q : Subgroup X) = ⊤ →
      ∀ Q₀ Q₁ : Subgroup X, IsCyclic Q₀ → Q₀ ≠ ⊥ → Nat.card Q₁ = p ^ 3 →
        ¬ IsMulCommutative Q₁ → (∀ q ∈ Q₁, q ^ p = 1) → (∀ a ∈ Q₀, ∀ b ∈ Q₁, a * b = b * a) →
        Q₀ ⊓ Q₁ = ⊥ → Q₀ ⊔ Q₁ = (Q : Subgroup X) →
        ∀ A : Subgroup X, A ≤ (Q : Subgroup X) → Nat.card A = p →
          ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) ∧
            A.map (MulAut.conj g).toMonoidHom ≠ A

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
