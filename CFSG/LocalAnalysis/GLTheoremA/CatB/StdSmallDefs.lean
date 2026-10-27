module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def StdSubCoverAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G), IsSStarMax 3 B x L → 3 ^ 4 ≤ Nat.card B →
    CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple 3 L) → InnerDiagMarking B L →
    GLAStdSubPre 3 B x L D K → SmallType 3 K → Subgroup.center ↥K ≠ ⊥ →
      IsPGroup 2 ↥(Subgroup.center ↥K) ∧
      (∀ z ∈ K, (∀ k ∈ K, k * z = z * k) → ∀ l ∈ L, l * z = z * l) ∧
      catalogIs (PSimple 3 L) (fun i => S9.isSp6two i ∨ S9.isU4two i ∨ S9.isD4two i)

@[expose] def StdSubInnerD4At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B L : Subgroup G), CFSG.Open.IsQuasisimple ↥L → catalogIs (PSimple 3 L) S9.isD4two →
    IsElemAbelian 3 B → InnerDiagMarking B L → ∀ b ∈ B, InducesInnerMod 3 L b

@[expose] def D4Rank4At : Prop :=
  ∀ (K : Type) [Group K] [Finite K], catalogIs K S9.isD4two →
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4

end CFSG.LocalAnalysis.GLTheoremA
