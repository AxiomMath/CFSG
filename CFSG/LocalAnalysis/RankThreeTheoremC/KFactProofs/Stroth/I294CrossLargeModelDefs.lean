module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open

@[expose] def I294LargeModelPSL : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (K : Type) [Field K] [Finite K], ¬ r ∣ Nat.card K →
    ∀ n : ℕ, ¬ (r ∣ n ∧ r ∣ Nat.card K - 1) →
      (∃ S : Sylow r (StatedProj (StatedSL n K)),
        ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedSL n K)))) →
      4 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedSL n K)))

@[expose] def I294LargeModelPSU : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ¬ r ∣ ℓ ^ f → ∀ n : ℕ, 3 ≤ n → ¬ (r ∣ n ∧ r ∣ ℓ ^ f + 1) →
      (∃ S : Sylow r (StatedProj (StatedSU n (ℓ ^ f) K)),
        ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))) →
      4 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedSU n (ℓ ^ f) K)))

@[expose] def I294LargeModelPSp : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (K : Type) [Field K] [Finite K], ¬ r ∣ Nat.card K →
    ∀ n : ℕ, 1 ≤ n →
      (∃ S : Sylow r (StatedProj (StatedSp n K)),
        ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedSp n K)))) →
      4 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedSp n K)))

@[expose] def I294LargeModelPOmegaOdd : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (K : Type) [Field K] [Finite K], ¬ r ∣ Nat.card K →
    Odd (Nat.card K) → ∀ n : ℕ, 3 ≤ n →
      (∃ S : Sylow r (StatedProj (StatedOmega (StatedQuadOdd n K))),
        ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K))))) →
      4 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K))))

@[expose] def I294LargeModelPOmegaPlus : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (K : Type) [Field K] [Finite K], ¬ r ∣ Nat.card K →
    ∀ n : ℕ, 4 ≤ n →
      (∃ S : Sylow r (StatedProj (StatedOmega (StatedQuadPlus n K))),
        ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))) →
      4 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))

@[expose] def I294LargeModelPOmegaMinus : Prop :=
  ∀ (r : ℕ), r.Prime → 5 ≤ r → ∀ (K : Type) [Field K] [Finite K], ¬ r ∣ Nat.card K →
    ∀ n : ℕ, 4 ≤ n → ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      (∃ S : Sylow r (StatedProj (StatedOmega (StatedQuadMinus n K b c))),
        ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))))) →
      4 ≤ pRank r (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
