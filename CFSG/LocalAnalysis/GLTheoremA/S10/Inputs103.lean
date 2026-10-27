module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I263UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L → IsChevSimple 2 (PSimple p L) →
    (∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p L) →
    IsGStar p B L ∨ (p = 3 ∧ GLAMarking (PQuot 3 L) (fun lab _ _ _ _ _ => lab.n = 1))

@[expose] def I131TD4At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A T : Subgroup G), GLAPComponent 3 X L → IsTD4 3 L →
    GLAMarking (PQuot 3 L) (fun lab _ _ _ _ _ => lab.n = 1) → A ≤ Subgroup.normalizer (L : Set G) →
    IsElemAbelian 3 A → T ≤ L → IsPGroup 2 T → A ≤ Subgroup.normalizer (T : Set G) →
    ¬ T ≤ GLAPPrimeCoreOf 3 L → Nat.card A ≤ 3 ^ 2 * Nat.card ↥(A ⊓ centModSubgroup 3 L)

@[expose] def I265UsedAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G) (b : G), IsSStarMax p B x L → IsChevSimple 2 (PSimple p L) →
    IsGStar p B L → b ∈ B → b ∉ Subgroup.zpowers x → R2Prop p b L →
    (p = 3 → IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L)) → Ipart p L b ≠ ⊥ →
    ¬ InnDiagOn p B L →
    (∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
        GLAPLayer p (L ⊓ cs E) ≠ ⊥) ∨
      (p = 3 ∧ catalogIs (PSimple 3 L) S9.isU4eight ∧ FieldOn 3 b L)

@[expose] def MultU48At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L : Subgroup G, CFSG.Open.IsQuasisimple ↥L → catalogIs (↥L ⧸ Subgroup.center ↥L) S9.isU4eight →
    catalogIs ↥L S9.isU4eight

@[expose] def I91U48At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (b : G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight → FieldOn 3 b L →
    catalogIs ↥(L ⊓ cx b) S9.isU4two ∧ centCard2 3 L b = 2 ^ 6

@[expose] def I1024aU42At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J E : Subgroup G), GLAPComponent 3 X J → catalogIs (PSimple 3 J) S9.isU4two → E ≤ J →
    IsElemAbelian 3 E → ∃ E' : Subgroup G, E ≤ E' ∧ E' ≤ J ∧ IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ 3

@[expose] def I1015U42At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L E T : Subgroup G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight → E ≤ L →
    IsElemAbelian 3 E → T ≤ L → IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set G) →
    ¬ T ≤ GLAPPrimeCoreOf 3 L → Nat.card E ≤ 3 ^ 2

@[expose] def I8U48At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L E₁ : Subgroup G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight → E₁ ≤ L →
    IsElemAbelian 3 E₁ → Nat.card E₁ = 3 ^ 3 →
    ∃ y ∈ E₁, y ≠ 1 ∧ ∃ E₀ : Subgroup G, E₀ ≤ E₁ ∧ IsElemAbelian 3 E₀ ∧ Nat.card E₀ = 3 ^ 2 ∧ y ∈ E₀ ∧
      GLAPComponent 3 (L ⊓ cx y) (GLAPLayer 3 (L ⊓ cx y)) ∧
        catalogIs (PSimple 3 (GLAPLayer 3 (L ⊓ cx y))) S9.isU3eight ∧
        GLAPLayer 3 (GLAPLayer 3 (L ⊓ cx y) ⊓ cs E₀) ≠ ⊥

@[expose] def I2018At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d x : G) (K J S₀ : Subgroup G), GLAPComponent 3 (cx d) K → CFSG.Open.IsKGroup ↥(cx d) → x ∈ cx d →
    x ^ 3 = 1 → x ∉ Subgroup.zpowers d →
    GLAPComponent 3 (K ⊓ cx x) J → catalogIs (PSimple 3 J) S9.isU3eight → S₀ ≤ K → IsPGroup 2 S₀ →
    ⁅S₀, J⁆ = S₀ → ¬ S₀ ≤ GLAPPrimeCoreOf 3 K → x ∈ Subgroup.normalizer (K : Set G) →
    IsChevSimple 2 (PSimple 3 K) ∧ ¬ IsTD4 3 K ∧
      GLAMarking (PQuot 3 K) (fun lab _ _ _ _ _ =>
        (lab.n = 1 ∧ 2 ^ 6 < card2 3 K) ∨ (lab.n = 3 ∧ 2 ^ 18 < card2 3 K))

@[expose] def I91CentPartAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X L : Subgroup G) (b : G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) → b ^ p = 1 →
    FieldOn p b L → centCard2 p L b ^ p = card2 p L

@[expose] def AutU48At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A : Subgroup G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight → A ≤ Subgroup.normalizer (L : Set G) →
    IsElemAbelian 3 A → ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A ≤ 3 * Nat.card A₀ ∧ ∀ a ∈ A₀, InducesInnerMod 3 L a

@[expose] def FieldNAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X L : Subgroup G) (g : G), GLAPComponent p X L → FieldOn p g L →
    GLAMarking (PQuot p L) (fun lab _ _ _ _ _ => p ∣ lab.n) ∧
      ¬ GLAMarking (PQuot p L) (fun lab _ _ _ _ _ => lab.n = 1) ∧
      ∀ N : ℕ, GLAMarking (PQuot p L) (fun lab _ _ _ _ _ => lab.n = N) → p ∣ N

@[expose] def I112SingleU38At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X : Subgroup G) (z : G) (E J : Subgroup G), CFSG.Open.IsKGroup ↥X → z ∈ E → E ≤ X → IsElemAbelian 3 E →
    3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card E →
    GLAPComponent 3 (X ⊓ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)) J →
    E ≤ Subgroup.normalizer (J : Set G) → catalogIs (PSimple 3 J) S9.isU3eight →
    ∃ K : Subgroup G, GLAPComponent 3 X K ∧ J ≤ K ∧ E ≤ Subgroup.normalizer (K : Set G)

end CFSG.LocalAnalysis.GLTheoremA
