module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

@[expose] def I264bAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsElemAbelian p B → x ∈ B →
    x ≠ 1 → GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L → CFSG.Open.IsKGroup ↥L →
    B ≤ Subgroup.normalizer (L : Set G) → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B (L ⊔ B) →
    IsChevSimple 2 (PSimple p L) →
    (∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p L) → IsGB p B L

@[expose] def I712At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X L A T : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L →
    IsChevSimple 2 (PSimple p L) → IsPGroup p A → IsPGroup 2 T →
    A ≤ Subgroup.normalizer (L : Set G) → T ≤ Subgroup.normalizer (L : Set G) →
    A ≤ Subgroup.normalizer (T : Set G) → ∀ a ∈ A, ∀ t ∈ T, InducesInnerMod p L ⁅a, t⁆

@[expose] def I9List93At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X L B : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent p X L →
    IsChevSimple 2 (PSimple p L) → fullCoverLevel p (PQuot p L) ≤ 2 → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set G) →
    p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B →
    ((∃ b ∈ B, ¬ InducesInnerMod p L b) ∨ p ∣ Nat.card (Subgroup.center (PQuot p L))) →
    catalogIs (PSimple p L) (S9.isList93 p)

@[expose] def I137At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y J I S : Subgroup G) (x : G), CFSG.Open.IsKGroup ↥Y → GLAPComponent p Y J →
    fullCoverLevel p (PQuot p J) ≤ 2 → S ≤ J → IsPGroup 2 S → ¬ S ≤ GLAPPrimeCoreOf p J →
    x ∈ Subgroup.normalizer (J : Set G) → x ^ p = 1 → ¬ CentMod p J x →
    GLAPComponent p (J ⊓ Subgroup.centralizer ({x} : Set G)) I →
    (∃ I₀ : Subgroup G, I₀ ≤ I ∧ I₀ ⊔ GLAPPrimeCoreOf p I = I ∧
      I₀ ≤ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G)) →
    x ∈ Subgroup.normalizer ((S ⊔ GLAPPrimeCoreOf p J : Subgroup G) : Set G) →
    catalogIs (PSimple p I) (S9.isList93 p) → p = 3 ∧ catalogIs (PSimple 3 I) S9.isL3four

@[expose] def I71SL34At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L B : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isL3four →
    IsElemAbelian 3 B → B ≤ Subgroup.normalizer (L : Set G) →
    Nat.card B ≤ 9 * Nat.card ↥(B ⊓ centModSubgroup 3 L)

@[expose] def K3NotChev2At : Prop :=
  ∀ (p : ℕ) (Q : Type) [Group Q], K3Cover p Q → ¬ IsChevSimple 2 (Q ⧸ Subgroup.center Q)

@[expose] def I269At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L D : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
    catalogIs (PSimple 3 L) S9.isList269 → IsElemAbelian 3 D →
    D ≤ Subgroup.normalizer (L : Set G) →
    Nat.card D = 3 ^ 2 * Nat.card ↥(D ⊓ centModSubgroup 3 L) →
    GLAPLayer 3 (L ⊓ Subgroup.centralizer (D : Set G)) = ⊥

@[expose] def I117At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLAIsBmax 3 B → IsEssential 3 B x →
    CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G)) →
    GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L → B ≤ Subgroup.normalizer (L : Set G) →
    catalogIs (PSimple 3 L) S9.isD4two → ∀ b ∈ B, InducesInnerMod 3 L b

@[expose] def Rank23At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isList94 →
    Subgroup.center (PQuot 3 L) = ⊥ ∧
    (∀ b ∈ Subgroup.normalizer (L : Set G), b ^ 3 = 1 → ¬ InducesInnerMod 3 L b →
      catalogIs (PSimple 3 L) S9.isD4two) ∧
    ∀ E T : Subgroup G, E ≤ L → IsElemAbelian 3 E → T ≤ L → IsPGroup 2 T →
      ¬ T ≤ GLAPPrimeCoreOf 3 L → E ≤ Subgroup.normalizer (T : Set G) →
      Nat.card E ≤ 27 ∧
        (catalogIs (PSimple 3 L) (fun i => S9.isSp6two i ∨ S9.isU4two i) → Nat.card E ≤ 9)

@[expose] def L94TypeHyAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L : Subgroup G, catalogIs (PSimple 3 L) S9.isList94 → Subgroup.center (PQuot 3 L) = ⊥ →
    ∃ y : PQuot 3 L, orderOf y = 3 ∧ ∃ W : Subgroup (PQuot 3 L), IsPGroup 2 W ∧ W ≠ ⊥ ∧
      y ∈ Subgroup.normalizer (W : Set (PQuot 3 L))

end CFSG.LocalAnalysis.GLTheoremA
