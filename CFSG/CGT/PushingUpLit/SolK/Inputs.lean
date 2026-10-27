module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.CGT.PushingUp.Defs
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)

@[expose] def SolomonTimmesfeldTight : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K,
        ((R : Subgroup K).map K.subtype = pCoreOf 2 K ∧
          ((IsCyclic ((R : Subgroup K).map K.subtype) ∧
              Nat.card ((R : Subgroup K).map K.subtype) = 4) ∨
            IsElemAbelian 2 ((R : Subgroup K).map K.subtype)) ∧
          ∃ g : G, conjSubgroup g ((R : Subgroup K).map K.subtype) ≤
              Subgroup.normalizer (K : Set G) ∧
            conjSubgroup g ((R : Subgroup K).map K.subtype) ≠ (R : Subgroup K).map K.subtype) ∨
        (IsCyclic K ∧ (HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G)) ∨
        (Nonempty (((R : Subgroup K).map K.subtype) ≃* QuaternionGroup 2) ∧
          (StatedClassicalModel G .PSL 3 3 1 ∨ StatedClassicalModel G .PSU 3 3 1 ∨
            CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
            CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
            CFSG.Blueprint.LieModel G .G2 0 3 1)) ∨
        ((∃ H : Subgroup G, H ≤ pCoreOf 2 K ∧ H ≤ (R : Subgroup K).map K.subtype ∧
            Nonempty (↥H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
            H.relIndex ((R : Subgroup K).map K.subtype) ≤ 2) ∧
          StatedClassicalModel G .PSL 3 2 2) ∨
        ((∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
          (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s)) ∨
        ((R : Subgroup K).map K.subtype = pCoreOf 2 K ∧
          IsElemAbelian 2 ((R : Subgroup K).map K.subtype) ∧
          4 ≤ Nat.card ((R : Subgroup K).map K.subtype) ∧
          IsTI ((R : Subgroup K).map K.subtype) ∧
          Subgroup.normalizer (((R : Subgroup K).map K.subtype : Subgroup G) : Set G) =
            Subgroup.normalizer (K : Set G) ∧
          WeaklyClosedIn ((R : Subgroup K).map K.subtype) (Subgroup.normalizer (K : Set G)))

@[expose] def WCBlockCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.Assembly.IsCharTwoType G →
    ∀ (R X : Subgroup G) (n : ℕ), 2 ≤ n → IsElemAbelian 2 R → 4 ≤ Nat.card R → IsTI R →
      IsMaximalTwoLocal (Subgroup.normalizer (R : Set G)) →
      WeaklyClosedIn R (Subgroup.normalizer (R : Set G)) →
      CFSG.maximalTwoLocalsContaining (X : Set G) = {Subgroup.normalizer (R : Set G)} →
      X ≤ Subgroup.normalizer (R : Set G) →
      (X.subgroupOf (Subgroup.normalizer (R : Set G))).Normal →
      IsShortGroup ↥X → IsNaturalAltModule ↥X n → X ≤ Subgroup.centralizer (R : Set G) → False

@[expose] def T75Structural : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    ∀ (Q X : Subgroup G) (n : ℕ), 2 ≤ n →
      IsElemAbelian 2 Q → IsTI Q → WeaklyClosedIn Q (Subgroup.normalizer (Q : Set G)) →
      Subgroup.centralizer (Q : Set G) = Q → X ≤ Subgroup.normalizer (Q : Set G) →
      (X.subgroupOf (Subgroup.normalizer (Q : Set G))).Normal →
      (CFSG.pCore 2 ↥X).map X.subtype ≤ Q →
      IsShortGroup ↥X → IsNaturalAltModule ↥X n → False

end CFSG.CGT.PushingUpLit.SolK
