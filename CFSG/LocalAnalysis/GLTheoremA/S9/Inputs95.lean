module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def I141At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X L E J : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L →
    IsChevSimple 2 (PSimple p L) → IsElemAbelian p E → E ≤ Subgroup.normalizer (L : Set G) →
    GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) J →
    Odd ((GLAPPrimeCoreOf p L).relIndex (GLAPPrimeCoreOf p J))

@[expose] def I2610At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L B : Subgroup G) (x : G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) (fun i => S9.isU6two i ∨ S9.isF4two i ∨ S9.isTE6two i) →
    IsElemAbelian 3 B → B ≤ Subgroup.normalizer (L : Set G) → x ≠ 1 →
    B ⊓ centModSubgroup 3 L = Subgroup.zpowers x → IsGB 3 B L →
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ B ⊓ centModSubgroup 3 L ≤ E ∧
      ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer (E : Set G)) J ∧
        ¬ catalogIs (PSimple 3 J) S9.isL2prime

@[expose] def I67At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X L B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L →
    IsChevSimple 2 (PSimple p L) → Even (Nat.card (GLAPPrimeCoreOf p L)) →
    Odd (Nat.card (⁅L, GLAPPrimeCoreOf p L⁆ : Subgroup G)) → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set G) →
    p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B →
    catalogIs (PSimple p L) S9.isList67

@[expose] def Rank3AutAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (X L B : Subgroup G), p.Prime → p ≠ 2 → GLAPComponent p X L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set G) →
    p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B →
    catalogIs (PSimple p L) S9.isList67 → p = 3

@[expose] def InvolvedSL2At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p q : ℕ) (X J : Subgroup G), p.Prime → q.Prime → q ≠ 2 → CFSG.Open.IsKGroup ↥X →
    GLAPComponent p X J → S9.InvolvedSL2 q (PSimple p J) → catalogIs (PSimple p J) S9.isL2prime

end CFSG.LocalAnalysis.GLTheoremA
