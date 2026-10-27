module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongGammaDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection IsParabolicTwo)

structure E3Setting {A : Type} [Group A] [Finite A] (K K₀ B : Subgroup A) (z : A) (p : ℕ) :
    Prop where
  hp : p.Prime
  hp5 : 5 ≤ p
  hKr : CFSG.Open.pRank p K ≤ 1
  hz : orderOf z = p
  hzK₀ : z ∈ K₀
  hpar : IsParabolicTwo A K K₀
  hne : K₀ ≠ K
  hcore : ∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ → ¬ U ≤ rankThreePrimeCore p K₀
  hB : IsElemAbelian p B
  hBc : Nat.card B = p ^ 2
  hzB : z ∈ B
  hBK : B ≤ normalizer (K : Set A)
  hBK₀ : B ≤ normalizer (K₀ : Set A)
  hnb : ∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b
  hℓ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.Open.pRank ℓ K ≤ 3

@[expose] def E3Concl {A : Type} [Group A] (K₀ B : Subgroup A) (z : A) (p : ℕ) : Prop :=
  ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
    B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
    p ∣ N.relIndex H ∧
    ∃ d : ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.IsE3LeviIndex d.1 ∧
      ∃ φ : ↥H →* (CFSGIndex.lie d).Group, Function.Surjective φ ∧
        φ.ker = N.subgroupOf H

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
