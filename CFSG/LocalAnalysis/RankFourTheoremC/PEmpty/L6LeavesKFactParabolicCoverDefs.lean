module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover
public import CFSG.LieType.SeitzGeneration.HyperLeaf

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open CFSG.LieType.SeitzGeneration (HyperGen)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover (EvenScope)

@[expose] def KFactParabolicLevi : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ : Subgroup A) (p : ℕ),
    IsChevSimple 2 ↥K → ¬ fusionIsBenderGroup ↥K → p.Prime → 5 ≤ p → CFSG.Open.pRank p K ≤ 1 →
    IsParabolicTwo A K K₀ → K₀ ≠ K →
    (∀ U : Subgroup A, CFSG.ABGLocalTools.IsSylowOf 2 U K₀ →
      ¬ U ≤ rankThreePrimeCore p K₀) →
    ∃ (f : ℕ) (H N : Subgroup A), f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ 2 ≤ CFSG.Open.pRank f K ∧
      H ≤ K₀ ∧ (H.subgroupOf K₀).Normal ∧ S622IsSimpleSection H N ∧ f ∣ N.relIndex H ∧
      p ∣ N.relIndex H ∧ ¬ p ∣ Nat.card N

@[expose] def KFactParabolicRadical : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K K₀ : Subgroup A),
    IsChevSimple 2 ↥K → ¬ fusionIsBenderGroup ↥K → IsParabolicTwo A K K₀ → K₀ ≠ K →
    pCoreOf 2 K₀ ≠ ⊥

@[expose] def KFactSeitzOutside : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (K E U : Subgroup A) (f : ℕ),
    IsChevSimple 2 ↥K → ¬ fusionIsBenderGroup ↥K →
    (∀ d : TauCeti.ValidLieTypeIndex, EvenScope d.1 →
      ¬ Nonempty (↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    f.Prime → f ≠ 2 → E ≤ K → IsElemAbelian f E → Nat.card E = f ^ 2 →
    U ≤ K → U ≠ ⊥ → IsPGroup 2 U → E ≤ normalizer (U : Set A) → HyperGen f K E

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
