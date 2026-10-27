module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def LBalanceEqAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → CFSG.Open.IsKProper G → ∀ D E : Subgroup G, IsPGroup p D → IsPGroup p E →
    (∀ d ∈ D, ∀ e ∈ E, d * e = e * d) →
    GLAPLayer p (GLAPLayer p (Subgroup.centralizer (D : Set G)) ⊓ Subgroup.centralizer (E : Set G)) =
      GLAPLayer p (Subgroup.centralizer (D : Set G) ⊓ Subgroup.centralizer (E : Set G))

@[expose] def RankAutSmallAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (X K A : Subgroup G), p.Prime → p ≠ 2 → GLAPComponent p X K → SmallType p K →
    A ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian p A →
    p ^ 2 * Nat.card ↥(A ⊓ centModSubgroup p K) ≤ Nat.card A → p = 3

@[expose] def I171OneAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G), p.Prime → p ≠ 2 → IsSStarMax p B x L →
    p ^ 4 ≤ Nat.card B → CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple p L) →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → InnerDiagMarking B L →
    GLAStdSubPre p B x L D K → InnDiagOn p B K

@[expose] def I171TwoAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax 3 B x L → 3 ^ 4 ≤ Nat.card B →
    CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple 3 L) →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → InnerDiagMarking B L →
    (∃ D K : Subgroup G, GLAStdSubPre 3 B x L D K) →
    (∀ D K : Subgroup G, GLAStdSubPre 3 B x L D K → GLASmall K) →
    catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i) ∧
      (∀ b ∈ B, InducesInnerMod 3 L b) ∧ ∀ D K : Subgroup G, GLAStdSubPre 3 B x L D K → U42Type 3 K

@[expose] def I265StdAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G), p.Prime → p ≠ 2 → IsSStarMax p B x L → p ^ 4 ≤ Nat.card B →
    CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple p L) →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → InnerDiagMarking B L → GLAStdSubPre p B x L D K →
    (∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (L ⊓ cs E) ≠ ⊥) ∨ (p = 3 ∧ SmallType 3 K)

@[expose] def I269SixAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L D : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) S9.isU6two → IsElemAbelian 3 D → D ≤ Subgroup.normalizer (L : Set G) →
    (∀ d ∈ D, InducesInnerMod 3 L d) →
    Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L) →
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥

@[expose] def LevelTwoAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i) →
    fullCoverLevel 3 (PQuot 3 L) = 2

@[expose] def StdSubSmallAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L D K : Subgroup G), IsSStarMax 3 B x L → 3 ^ 4 ≤ Nat.card B →
    CFSG.Open.IsQuasisimple ↥L → IsChevSimple 2 (PSimple 3 L) → InnerDiagMarking B L →
    GLAStdSubPre 3 B x L D K → SmallType 3 K → GLASmall K

end CFSG.LocalAnalysis.GLTheoremA
