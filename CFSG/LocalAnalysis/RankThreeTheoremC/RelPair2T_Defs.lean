module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

structure IsPSignalizer {X : Type*} [Group X] (p : ℕ) (D : Subgroup X) (d : X)
    (O : Subgroup X) : Prop where
  le_centralizer : O ≤ centralizer ({d} : Set X)
  normal : centralizer ({d} : Set X) ≤ normalizer (O : Set X)
  coprime : p.Coprime (Nat.card O)
  le : ∀ W : Subgroup X, W ≤ centralizer ({d} : Set X) → p.Coprime (Nat.card W) →
    D ≤ normalizer (W : Set X) → W ≤ O

structure ThompsonFrame (p : ℕ) {X : Type} [Group X] [Finite X] (D : Subgroup X) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  pCore_eq_bot : CFSG.pCore p X = ⊥
  pPrimeCore_eq_bot : CFSG.pPrimeCore p X = ⊥
  rank_le : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2
  sylow : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set X))
  signalizer : ∀ d ∈ D, d ≠ 1 → ∃ O : Subgroup X, IsPSignalizer p D d O
  join : p ∣ Nat.card (invariantTwoJoinIn D (⊤ : Subgroup X))

structure ThompsonPreFrame (p : ℕ) {Y : Type} [Group Y] [Finite Y] (K D : Subgroup Y)
    [K.Normal] : Prop where
  prime : p.Prime
  odd : p ≠ 2
  coprime : p.Coprime (Nat.card K)
  max : ∀ N : Subgroup Y, N.Normal → p.Coprime (Nat.card N) → N ≤ K
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  pCore_quot : CFSG.pCore p (Y ⧸ K) = ⊥
  rank_le : ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E ≤ p ^ 2
  sylow : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set Y))
  signalizer : ∀ d ∈ D, d ≠ 1 → ∃ O : Subgroup Y, IsPSignalizer p D d O
  join : p ∣ Nat.card (invariantTwoJoinIn D (⊤ : Subgroup Y))

end CFSG.LocalAnalysis.RankThreeTheoremC
