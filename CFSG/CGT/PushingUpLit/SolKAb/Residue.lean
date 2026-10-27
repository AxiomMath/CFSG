module

public import CFSG.CGT.PushingUpLit.SolKMT.Statement
public import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.CGT.PushingUpLit.SolKAb

open CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.Assembly.LowTwoRank
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)
open CFSG.RankThree.PartTwo (omegaOneSub)
open CFSG.CGT.PushingUpLit.SolKMT (SolomonTimmesfeldMain)

@[expose] def MTOutcome (G : Type) [Group G] (K : Subgroup G) (R : Sylow 2 K) : Prop :=
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

theorem solomonTimmesfeldMain_iff :
    SolomonTimmesfeldMain ↔
      ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
        (∃ a b : G, a * b ≠ b * a) →
        ∀ K : Subgroup G, TightlyEmbedded K →
          IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
          Subgroup.normalizer (K : Set G) ⊓
              Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
            pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
          ∀ R : Sylow 2 K, MTOutcome G K R :=
  Iff.rfl

@[expose] def SolomonTimmesfeldMainNonAbelian : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K,
        ¬ (∀ a ∈ (R : Subgroup K).map K.subtype, ∀ b ∈ (R : Subgroup K).map K.subtype,
            a * b = b * a) →
        MTOutcome G K R

@[expose] def SolomonTimmesfeldMainRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K,
        (∀ a ∈ (R : Subgroup K).map K.subtype, ∀ b ∈ (R : Subgroup K).map K.subtype,
            a * b = b * a) →
        ¬ IsElemAbelian 2 ((R : Subgroup K).map K.subtype) →
        Nat.card ↥(omegaOneSub ((R : Subgroup K).map K.subtype)) = 4 →
        (∃ H : Subgroup G, (∀ x : G, x ∈ H ↔ x ∈ (R : Subgroup K).map K.subtype ∧ x ^ 4 = 1) ∧
          Nonempty (↥H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) →
        MTOutcome G K R

structure SolomonTimmesfeldMainResidue : Prop where
  nonabelian : SolomonTimmesfeldMainNonAbelian
  rankTwo : SolomonTimmesfeldMainRankTwo

end CFSG.CGT.PushingUpLit.SolKAb
