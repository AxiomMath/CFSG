module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure AutCalcAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  field_nonInnDiag : ∀ (X L : Subgroup G) (g : G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) →
    FieldOn p g L → NonInnDiag p g L
  td4_nonInnDiag : ∀ (X L : Subgroup G) (g : G), GLAPComponent p X L → IsTD4 p L →
    NonInner p g L → NonInnDiag p g L
  inner_innDiag : ∀ (X L : Subgroup G) (g : G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) →
    g ∈ Subgroup.normalizer (L : Set G) → InducesInnerMod p L g → InnDiagOn p (Subgroup.zpowers g) L
  innDiag_unif : ∀ (X L A : Subgroup G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) →
    A ≤ Subgroup.normalizer (L : Set G) → (∀ a ∈ A, InnDiagOn p (Subgroup.zpowers a) L) →
    InnDiagOn p A L
  td4_not_field : ∀ (X L : Subgroup G) (g : G), GLAPComponent p X L → p = 3 → IsTD4 3 L →
    ¬ FieldOn 3 g L

@[expose] def FieldDichotomyAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSTriple p B x L →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) → IsChevSimple 2 (PSimple p L) →
    ∀ b ∈ B, NonInnDiag p b L → FieldOn p b L ∨ (p = 3 ∧ IsTD4 3 L)

@[expose] def FieldCentIndepAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X L B : Subgroup G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) → IsElemAbelian p B →
    ∀ b ∈ B, ∀ b' ∈ B, FieldOn p b L → FieldOn p b' L → centCard2 p L b = centCard2 p L b'

@[expose] def CentTD4At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (g : G), GLAPComponent 3 X L → IsChevSimple 2 (PSimple 3 L) → IsTD4 3 L → g ^ 3 = 1 →
    NonInner 3 g L → centCard2 3 L g ≤ Nat.sqrt (card2 3 L)

@[expose] def Chev2DownAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K : Subgroup G) (y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    y ^ p = 1 → y ∈ Subgroup.normalizer (K : Set G) → IsChevSimple 2 (PSimple p K) →
    ∀ J : Subgroup G, GLAPComponent p (K ⊓ Subgroup.centralizer ({y} : Set G)) J →
      IsChevSimple 2 (PSimple p J)

@[expose] def I148At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (x : G), GLAPComponent 3 X L → IsTD4 3 L → x ^ 3 = 1 →
    InnDiagOn 3 (Subgroup.zpowers x) L → ¬ CentMod 3 L x → centCard2 3 L x ^ 2 ≤ card2 3 L

@[expose] def I155At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X K : Subgroup G) (x y : G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X K →
    IsChevSimple 2 (PSimple p K) → x ∈ X → x ^ p = 1 → y ^ p = 1 → x * y = y * x →
    y ∉ Subgroup.zpowers x → y ∈ Subgroup.normalizer (K : Set G) →
    ((x ∈ Subgroup.normalizer (K : Set G) ∧ ¬ CentMod p K x) →
      InnDiagOn p (Subgroup.zpowers x) K ∧ FieldOn p y K) →
    ∀ J : Subgroup G, GLAPComponent p (closureIn K (Subgroup.zpowers x) ⊓ Subgroup.centralizer ({x} : Set G)) J →
      y ∈ Subgroup.normalizer (J : Set G) →
      (NonInnDiag p y J ∧ ¬ (p = 3 ∧ IsTD4 3 J)) ∨
        (¬ (x ∈ Subgroup.normalizer (K : Set G) ∧ ¬ CentMod p K x) ∧
          ∃ e : PSimple p J ≃* PSimple p K, IsoPresAct p y J K e)

structure R2Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  aut : AutCalcAt G p
  indep : FieldCentIndepAt G p
  cent : CentTD4At G

end CFSG.LocalAnalysis.GLTheoremA
