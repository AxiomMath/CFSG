module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {G : Type} [Group G]

@[expose] def I66At : Prop :=
  (∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    catalogIs (K ⧸ Subgroup.center K) isSporIndex →
    ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ g : K, g ^ 3 ≠ z) ∧
  (∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    catalogIs (K ⧸ Subgroup.center K) isSporIndex → ∀ p : ℕ, p.Prime → 5 ≤ p →
    GLAPPrimeCore p K = ⊥ → Subgroup.center K = ⊥)

@[expose] def I1017At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLAIsBmax p B →
    4 ≤ GLATwoLocalRank p G → x ∈ B → x ≠ 1 → GLAPComponent p (cx x) L →
    CFSG.Open.IsKGroup ↥(cx x) → B ≤ Subgroup.normalizer (L : Set G) →
    catalogIs (PSimple p L) isSporIndex → (∀ b ∈ B, CentMod p L b ↔ b ∈ Subgroup.zpowers x) →
    (∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) → Nat.card A ≤ p) →
    (∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ (⁅T, B⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p L) →
    ((∃ row : Row, RowL row p L) ∨
      (p = 3 ∧ (catalogIs (PSimple 3 L) (sporIs .ONan) ∨ catalogIs (PSimple 3 L) (sporIs .HN)))) ∧
    (∀ row : Row, RowL row p L →
      ∃ E : Subgroup G, E ≤ L ⊔ B ∧ IsElemAbelian p E ∧ Nat.card B < Nat.card E)

@[expose] def I301AAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (x : G) (L : Subgroup G) (row : Row), x ≠ 1 → orderOf x = p → GLAPComponent p (cx x) L →
    CFSG.Open.IsKGroup ↥(cx x) → RowL row p L → Odd (Nat.card (GLAPPrimeCoreOf p (cx x))) →
    (∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) → Nat.card A ≤ p) →
    GLATwoLocalRank p G ≤ row.rank → Nonempty (SporCfg G p x L row)

@[expose] def I1016RowAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (x : G) (L : Subgroup G) (row : Row), x ≠ 1 → orderOf x = p → GLAPComponent p (cx x) L →
    CFSG.Open.IsKGroup ↥(cx x) → RowL row p L →
    (∀ A : Subgroup G, IsElemAbelian p A → A ≤ cx x → (∀ a ∈ A, CentMod p L a) → Nat.card A ≤ p) →
    ∀ E V : Subgroup G, E ≤ L ⊔ Subgroup.zpowers x → IsElemAbelian p E → V ≤ L → IsPGroup 2 V →
      ¬ V ≤ GLAPPrimeCoreOf p L → E ≤ Subgroup.normalizer (V : Set G) → Nat.card E ≤ p ^ row.rank

@[expose] def TimmesfeldAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    IsCharTwoType G → ∀ M : Subgroup G, GLAIsMaxTwoLocal M → IsExtraSpec2 (pCoreOf 2 M) →
      2 ^ 25 ≤ Nat.card ↥(pCoreOf 2 M) → (∃ g ∈ M, orderOf g = 5) →
      IsSimpleGroup ↥(oPrimeRes 5 (↥M ⧸ GLAPPrimeCore 5 ↥M))

@[expose] def No5PumpupAt : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    CFSG.Open.IsKGroup Y → ∀ y : Y, orderOf y = 5 → ∀ J : Subgroup Y,
      GLAPComponent 5 (cx y) J → ¬ catalogIs (PSimple 5 J) (sporIs .Co1)

@[expose] def I1016Co2At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) (sporIs .Co2) →
    Nat.card (Subgroup.center (PQuot 3 L)) = 1 ∧
    (∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4) ∧
    (∃ E V : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ V ≤ L ∧ IsPGroup 2 V ∧
      ¬ V ≤ GLAPPrimeCoreOf 3 L ∧ E ≤ Subgroup.normalizer (V : Set G))

end CFSG.LocalAnalysis.GLTheoremA
