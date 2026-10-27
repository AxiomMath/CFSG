module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def IsE3LeviIndex : TauCeti.LieTypeIndex → Prop
  | .A 1 _ => True
  | .A 2 _ => True
  | .B 2 _ => True
  | .C 2 _ => True
  | .twistedA 3 _ => True
  | _ => False

@[expose] def KFactGammaParaE3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ B : Subgroup A) (z : A) (p : ℕ),
    IsChevSimple 2 ↥K → p.Prime → 5 ≤ p → CFSG.Open.pRank p K ≤ 1 → orderOf z = p → z ∈ K₀ →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ → ¬ U ≤ rankThreePrimeCore p K₀) →
    IsElemAbelian p B → Nat.card B = p ^ 2 → z ∈ B → B ≤ normalizer (K : Set A) →
    B ≤ normalizer (K₀ : Set A) →
    (∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b) →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.Open.pRank ℓ K ≤ 3) →
    ∃ y ∈ B, y ∉ zpowers z ∧
      ¬ CFSG.HallHigman.IsPSolvable p ↥(K₀ ⊓ centralizer ({y} : Set A))

@[expose] def KFactGammaLevi : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ B : Subgroup A) (z : A) (p : ℕ),
    IsChevSimple 2 ↥K → p.Prime → 5 ≤ p → CFSG.Open.pRank p K ≤ 1 → orderOf z = p → z ∈ K₀ →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ → ¬ U ≤ rankThreePrimeCore p K₀) →
    IsElemAbelian p B → Nat.card B = p ^ 2 → z ∈ B → B ≤ normalizer (K : Set A) →
    B ≤ normalizer (K₀ : Set A) →
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        ∃ φ : ↥H →* (TauCeti.CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H

@[expose] def KFactGammaLeviE3 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ B : Subgroup A) (z : A) (p : ℕ),
    IsChevSimple 2 ↥K → p.Prime → 5 ≤ p → CFSG.Open.pRank p K ≤ 1 → orderOf z = p → z ∈ K₀ →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ → ¬ U ≤ rankThreePrimeCore p K₀) →
    IsElemAbelian p B → Nat.card B = p ^ 2 → z ∈ B → B ≤ normalizer (K : Set A) →
    B ≤ normalizer (K₀ : Set A) →
    (∀ b ∈ B, b ≠ 1 → ¬ ∀ k ∈ K, b * k = k * b) →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → CFSG.Open.pRank ℓ K ≤ 3) →
    ∃ H N : Subgroup A, H ≤ K₀ ∧ S622IsSimpleSection H N ∧
      B ≤ normalizer (H : Set A) ∧ B ≤ normalizer (N : Set A) ∧ z ∈ H ∧ ¬ p ∣ Nat.card N ∧
      p ∣ N.relIndex H ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ d.1 ≠ .suzuki 2 ∧
        IsE3LeviIndex d.1 ∧
        ∃ φ : ↥H →* (TauCeti.CFSGIndex.lie d).Group, Function.Surjective φ ∧
          φ.ker = N.subgroupOf H

@[expose] def KFactFieldAutLieE3 : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (d : TauCeti.ValidLieTypeIndex) (p : ℕ),
    d.1.characteristic = 2 → d.1 ≠ .suzuki 2 → IsE3LeviIndex d.1 →
    Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group) → p.Prime → 5 ≤ p →
    CFSG.Open.pRank p (⊤ : Subgroup J) ≤ 1 → p ∣ Nat.card J →
    ∀ α : MulAut J, α ^ p = 1 → α ∉ inner J →
      ¬ CFSG.HallHigman.IsPSolvable p ↥(fixedSubgroup α)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
