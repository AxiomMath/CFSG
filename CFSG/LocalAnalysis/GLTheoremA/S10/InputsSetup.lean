module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I2023C3 {G : Type} [Group G] [Finite G] (x : G) (L : Subgroup G) : Prop :=
  ∀ g ∈ Subgroup.centralizer ({x} : Set G),
    (∀ l ∈ L, l⁻¹ * (g⁻¹ * l * g) ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))) →
      ∃ n : ℕ, g ^ (3 ^ n) ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G))

@[expose] def Lemma103PowCore (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (_ : p.Prime) (_ : p ≠ 2) {X L : Subgroup G} {x : G},
    GLAPComponent p X L → GLAPLayer p X = L → X ≤ Subgroup.normalizer (L : Set G) →
    CycModSylow p L → x ∈ X → orderOf x = p → (∀ g ∈ X, g * x = x * g) →
    ∀ y ∈ X ⊓ centModSubgroup p L, ∃ n : ℕ, y ^ (p ^ n) ∈ GLAPPrimeCoreOf p X

@[expose] def I2023At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G) (b₀ : G), IsSStarMax 3 B x L → IsChevSimple 2 (PSimple 3 L) →
    IsTD4 3 L → b₀ ∈ B → NonInner 3 b₀ L → 3 ^ 4 ≤ Nat.card B → I2023C3 x L →
    ∃ (B' : Subgroup G) (b : G), IsSTriple 3 B' x L ∧ B' ≤ Subgroup.normalizer (L : Set G) ∧
      b ∈ B' ∧ b ∉ Subgroup.zpowers x ∧ NonInner 3 b L ∧ centCard2 3 L b = Nat.sqrt (card2 3 L)

@[expose] def I156At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G) (b : G), IsSStarMax p B x L → IsChevSimple 2 (PSimple p L) →
    (∀ c ∈ B, NonInnDiag p c L → FieldOn p c L ∨ (p = 3 ∧ IsTD4 3 L)) → b ∈ B → R2Prop p b L →
    (p = 3 → IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L)) →
    p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B →
    (Ipart p L b ≠ ⊥ ∧
      (∀ c ∈ B, CentMod p (Ipart p L b) c ↔ c ∈ Subgroup.zpowers b ⊔ (B ⊓ centModSubgroup p L)) ∧
      InnDiagOn p B (Ipart p L b)) ∨
    (p = 3 ∧ catalogIs (PSimple 3 L) S9.isU3eight)

@[expose] def I2021At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G) (b : G), IsSStarMax p B x L → IsChevSimple 2 (PSimple p L) →
    b ∈ B → b ∉ Subgroup.zpowers x →
    R2Prop p b L → (p = 3 → IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L)) →
    p ^ 3 * Nat.card ↥(B ⊓ centModSubgroup p L) ≤ Nat.card B →
    (∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf p L) →
    ∃ a ∈ B, a ∉ Subgroup.zpowers x ∧ R2Prop p a L ∧
      (p = 3 → IsTD4 3 L → centCard2 3 L a = Nat.sqrt (card2 3 L)) ∧
      ∃ T : Subgroup G, T ≤ Ipart p L a ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
        ¬ T ≤ GLAPPrimeCoreOf p (Ipart p L a)

@[expose] def I91CentIAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X L : Subgroup G) (b : G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) → b ^ p = 1 →
    R2Prop p b L → Ipart p L b ≠ ⊥ → centCard2 p L b ≤ 2 * card2 p (Ipart p L b)

@[expose] def U38RankAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x : G) (L : Subgroup G), orderOf x = 3 → GLAPComponent 3 (Subgroup.centralizer ({x} : Set G)) L →
    catalogIs (PSimple 3 L) S9.isU3eight → CycModSylow 3 L → GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) = L →
    ∀ E T : Subgroup G, E ≤ Subgroup.centralizer ({x} : Set G) → IsElemAbelian 3 E →
      T ≤ Subgroup.centralizer ({x} : Set G) → IsPGroup 2 T →
      E ≤ Subgroup.normalizer (T : Set G) → ¬ T ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) →
      Nat.card E ≤ 3 ^ 3

@[expose] def LevelU38At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isU3eight →
    fullCoverLevel 3 (PQuot 3 L) ≤ 2

@[expose] def TD4G2At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (b' : G), GLAPComponent 3 X L → IsChevSimple 2 (PSimple 3 L) →
    catalogIs (PSimple 3 L) (onLie isTrialityD4Big) → b' ∈ Subgroup.normalizer (L : Set G) → b' ^ 3 = 1 →
    ¬ InducesInnerMod 3 L b' → centCard2 3 L b' = Nat.sqrt (card2 3 L) →
    ∀ a : G, a ∈ Subgroup.normalizer (L : Set G) → a ^ 3 = 1 → a * b' = b' * a →
      GLAPLayer 3 (L ⊓ cx b' ⊓ cx a) ≠ ⊥

@[expose] def TD42PerfAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L F : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isTD4two → IsElemAbelian 3 F →
    F ≤ Subgroup.normalizer (L : Set G) → Nat.card F = 3 ^ 2 → (∀ g ∈ F, CentMod 3 L g → g = 1) →
    ∀ K : Subgroup G, K ≤ L ⊓ Subgroup.centralizer (F : Set G) → (⁅K, K⁆ : Subgroup G) = K →
      K ≤ GLAPPrimeCoreOf 3 L

structure SetupInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  aut : AutCalcAt G p
  dich : FieldDichotomyAt G p
  indep : FieldCentIndepAt G p
  cent : CentTD4At G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i91 : I91CentIAt G p
  u38 : U38RankAt G
  i269 : I269At G
  lbal : LBalanceAt G 3
  lvl : LevelU38At G
  i91g : I91At G
  i147 : I147At G
  g2 : TD4G2At G
  perf : TD42PerfAt G

end CFSG.LocalAnalysis.GLTheoremA
