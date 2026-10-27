module

public import CFSG.CGT.PushingUp.Defs
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.CGT.PushingUpLit.SolKMT

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)

@[expose] def SolomonTimmesfeldMain : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K,
        (IsCyclic K ∧ Nat.card K = 4) ∨
        ((R : Subgroup K).map K.subtype = pCoreOf 2 K ∧
          IsElemAbelian 2 ((R : Subgroup K).map K.subtype)) ∨
        (Nonempty (((R : Subgroup K).map K.subtype) ≃* QuaternionGroup 2) ∧
          (StatedClassicalModel G .PSL 3 3 1 ∨ StatedClassicalModel G .PSU 3 3 1 ∨
            CFSG.Blueprint.LieModel G .G2 0 3 1 ∨
            CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
            CFSG.Blueprint.NativeSporadic.IsSporadic G .M12)) ∨
        ((R : Subgroup K).map K.subtype = K ∧ IsCyclic K ∧ 8 ≤ Nat.card K ∧
          (HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G)) ∨
        ((∃ H : Subgroup G, H ≤ pCoreOf 2 K ∧ H ≤ (R : Subgroup K).map K.subtype ∧
            Nonempty (↥H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) ∧
            H.relIndex ((R : Subgroup K).map K.subtype) ≤ 2) ∧
          StatedClassicalModel G .PSL 3 2 2) ∨
        ((R : Subgroup K).map K.subtype = pCoreOf 2 K ∧
          ((∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
            (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s)))

end CFSG.CGT.PushingUpLit.SolKMT
