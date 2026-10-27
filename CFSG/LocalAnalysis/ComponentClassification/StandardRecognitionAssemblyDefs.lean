module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalClassical

public section

namespace CFSG.ComponentClassification.StandardRecognition

open CFSG.Assembly

@[expose] def QuaternionStandardFrontier : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      (∃ r : ℕ, 3 ≤ r ∧ Nonempty
        ((S : Subgroup (Subgroup.centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (r - 2)))) →
      Models.OddLieType G ∨ Blueprint.NativeSporadic.IsSporadic G .M11 ∨
        Blueprint.NativeSporadic.IsSporadic G .M12

@[expose] def M12J2DoubleCoverExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
    (∀ x : G, orderOf x = 2 → Assembly.oddCore (Subgroup.centralizer ({x} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
      Nat.card (Subgroup.center L) = 2 →
      ¬ (Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
        Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2)

@[expose] def M12J2CentralTwoGroupOrderBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Assembly.IsQuasisimple L →
    IsPGroup 2 (Subgroup.center L) →
    (Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2) →
    Nat.card (Subgroup.center L) ≤ 2

@[expose] def RankSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    Assembly.ComponentType.IsStandardSubgroup L → ∀ S : Sylow 2 (Subgroup.centralizer (L : Set G)),
      2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (L : Set G)) ∨
      (IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) ∧
        (S : Subgroup (Subgroup.centralizer (L : Set G))) ≠ ⊥) ∨
      ∃ n : ℕ, 3 ≤ n ∧
        Nonempty
          ((S : Subgroup (Subgroup.centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (n - 2))) ∧
        ∃ t : Subgroup.centralizer (L : Set G), t ∈ S ∧ orderOf t = 2 ∧
          (∀ x ∈ S, orderOf x = 2 → x = t) ∧ SmallLocal.ClassicalInvolution (t : G)

@[expose] def TypePartition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
      Blueprint.Recognition.OddStandardType (L ⧸ Subgroup.center L) ∨
        (Blueprint.Recognition.EvenStandardType (L ⧸ Subgroup.center L) ∧
          ¬ Blueprint.Recognition.EvenStandardException (L ⧸ Subgroup.center L))

@[expose] def TauCetiPartition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    (InCatalog G ↔
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
        Models.OddLieType G ∨ Models.EvenLieType G ∨ Blueprint.NativeSporadic.SporadicRep G)

theorem tauCetiPartition_of_all
    (h : ∀ (G : Type) [Group G], (∃ a b : G, a * b ≠ b * a) →
      (InCatalog G ↔
        (∃ n : ℕ, 5 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
          Models.OddLieType G ∨ Models.EvenLieType G ∨ Blueprint.NativeSporadic.SporadicRep G)) :
    TauCetiPartition :=
  fun G _ _ _ hnonab => h G hnonab

@[expose] def StandardRecognitionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → ∀ L : Subgroup G, Assembly.ComponentType.IsStandardSubgroup L →
      InCatalog G

end CFSG.ComponentClassification.StandardRecognition
