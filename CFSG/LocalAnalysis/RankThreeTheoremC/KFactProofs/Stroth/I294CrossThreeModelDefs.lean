module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open

@[expose] def I294CrossModelPSL4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ∣ Nat.card K - 1 →
    ∀ x : StatedProj (StatedSL 4 K), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedSL 4 K))))

@[expose] def I294CrossModelPSL67 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ¬ 3 ∣ Nat.card K - 1 →
    ∀ n : ℕ, (n = 6 ∨ n = 7) → ∀ x : StatedProj (StatedSL n K), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedSL n K))))

@[expose] def I294CrossModelPSU4 : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = q ^ 2 → 3 ∣ q + 1 →
    ∀ x : StatedProj (StatedSU 4 q K), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedSU 4 q K))))

@[expose] def I294CrossModelPSU67 : Prop :=
  ∀ (q : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = q ^ 2 → ¬ 3 ∣ q → ¬ 3 ∣ q + 1 →
    ∀ n : ℕ, (n = 6 ∨ n = 7) → ∀ x : StatedProj (StatedSU n q K), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedSU n q K))))

@[expose] def I294CrossModelPSp6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K →
    ∀ x : StatedProj (StatedSp 3 K), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedSp 3 K))))

@[expose] def I294CrossModelPOmega7 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → Odd (Nat.card K) →
    ∀ x : StatedProj (StatedOmega (StatedQuadOdd 3 K)), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer ({x} : Set (StatedProj (StatedOmega (StatedQuadOdd 3 K)))))

@[expose] def I294CrossModelPOmegaMinus4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
    ∀ x : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)), orderOf x = 3 →
      3 ≤ pRank 3 (Subgroup.centralizer
        ({x} : Set (StatedProj (StatedOmega (StatedQuadMinus 4 K b c)))))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
