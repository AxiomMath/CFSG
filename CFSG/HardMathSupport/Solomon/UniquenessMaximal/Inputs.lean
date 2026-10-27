module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.LocalAnalysis.GLTheoremB.UniqStatements

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def Input33_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsCharTwoType G → ∀ T : Sylow 2 G, ∀ U : Subgroup G,
    IsUGroup 2 (T : Subgroup G) U → ∀ Y : Subgroup G, Odd (Nat.card Y) →
      U ≤ Subgroup.normalizer (Y : Set G) → U ≤ Subgroup.centralizer (Y : Set G)

@[expose] def Input10_20_3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) [Y.Normal] (K : Type) [Group K] [Finite K]
    (r : ℕ), IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty ((X ⧸ Y) ≃* (Fin r → K)) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      (1 ≤ GLATwoLocalRank q K → r ≤ GLATwoLocalRank q X) ∧
        (1 ≤ pRank q (⊤ : Subgroup K) → r ≤ pRank q (⊤ : Subgroup X))

@[expose] def InputOddTwoLocal : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ GLATwoLocalRank r K

@[expose] def InputUExists : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ P : Sylow 2 G, ∃ U : Subgroup G, IsUGroup 2 (P : Subgroup G) U

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
