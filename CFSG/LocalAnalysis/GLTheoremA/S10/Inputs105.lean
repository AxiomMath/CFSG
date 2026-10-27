module

public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def I2015At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X J I I₀ : Subgroup G) (d : G), GLAPComponent p X J → IsChevSimple 2 (PSimple p J) →
    GLAPComponent p (J ⊓ cx d) I → I₀ ≤ I → I₀ ⊔ GLAPPrimeCoreOf p I = I → d ^ p = 1 → R2Prop p d J →
    ∀ S : Subgroup G, S ≤ J → IsPGroup 2 S → I₀ ≤ Subgroup.normalizer (S : Set G) →
      S ≤ GLAPPrimeCoreOf p J

@[expose] def I1312At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p.Prime → p ≠ 2 → ∀ (X I B S : Subgroup G), GLAPComponent p X I → IsChevSimple 2 (PSimple p I) → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (I : Set G) → S ≤ I → IsPGroup 2 S → B ≤ Subgroup.normalizer (S : Set G) →
    ¬ S ≤ GLAPPrimeCoreOf p I →
    (∀ S' : Subgroup G, S ≤ S' → S' ≤ I → IsPGroup 2 S' → B ≤ Subgroup.normalizer (S' : Set G) →
      ¬ S' ≤ GLAPPrimeCoreOf p I → S' = S) →
    (∀ c ∈ B, (⁅S, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p I → CentMod p I c) ∧
      (Nat.card S ≤ 8 → ∃ B₀ : Subgroup G, B₀ ≤ B ∧ Nat.card B ≤ p * Nat.card B₀ ∧
        ∀ c ∈ B₀, (⁅S, Subgroup.zpowers c⁆ : Subgroup G) ≤ GLAPPrimeCoreOf p I)

@[expose] def I114At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X B K : Subgroup G), CFSG.Open.IsKGroup ↥X → B ≤ X → GLAIsBmax 3 B → GLAPComponent 3 X K →
    ¬ B ≤ Subgroup.normalizer (K : Set G) → catalogIs (PSimple 3 K) S9.isL3char2 →
    Nat.card (Subgroup.center (PQuot 3 K)) = 3 →
    ∀ T : Subgroup G, T ≤ closureIn K B → IsPGroup 2 T → B ≤ Subgroup.normalizer (T : Set G) →
      T ≤ GLAPPrimeCoreOf 3 (closureIn K B)

@[expose] def I1015oneAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L B T : Subgroup G), GLAPComponent 3 X L → B ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 B →
    3 ^ 3 * Nat.card ↥(B ⊓ centModSubgroup 3 L) ≤ Nat.card B → T ≤ L → IsPGroup 2 T →
    B ≤ Subgroup.normalizer (T : Set G) → ¬ T ≤ GLAPPrimeCoreOf 3 L →
    ¬ catalogIs (PSimple 3 L) (fun i => S9.isSp4eight i ∨ S9.isU3char2 i)

@[expose] def I91CompAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (X L : Subgroup G) (b : G), GLAPComponent p X L → IsChevSimple 2 (PSimple p L) → b ^ p = 1 →
    R2Prop p b L → Ipart p L b ≠ ⊥ →
    GLAPComponent p (L ⊓ cx b) (Ipart p L b) ∧ IsChevSimple 2 (PSimple p (Ipart p L b))

structure I91TypeAt (G : Type) [Group G] [Finite G] : Prop where
  exc : ∀ (X L : Subgroup G) (b : G), GLAPComponent 3 X L → IsChevSimple 2 (PSimple 3 L) → b ^ 3 = 1 →
    R2Prop 3 b L → (IsTD4 3 L → centCard2 3 L b = Nat.sqrt (card2 3 L)) →
    GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) → Ipart 3 L b ≠ ⊥ →
    catalogIs (PSimple 3 (Ipart 3 L b)) excIndex →
    catalogIs (PSimple 3 L) (fun i => S9.isSp4eight i ∨ S9.isL3char2 i ∨ S9.isU3char2 i)
  l3 : ∀ (X L : Subgroup G) (b : G), GLAPComponent 3 X L → b ^ 3 = 1 → R2Prop 3 b L →
    GLAPComponent 3 (L ⊓ cx b) (Ipart 3 L b) → Ipart 3 L b ≠ ⊥ →
    catalogIs (PSimple 3 L) S9.isL3char2 → catalogIs (PSimple 3 (Ipart 3 L b)) S9.isL3char2

@[expose] def ExcNoFieldAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X J : Subgroup G) (d : G), GLAPComponent 3 X J → IsExcType 3 J → ¬ FieldOn 3 d J

@[expose] def AutL3At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A : Subgroup G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isL3char2 →
    A ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 A →
    Nat.card A ≤ 3 ^ 3 * Nat.card ↥(A ⊓ centModSubgroup 3 L)

@[expose] def SL3TorusAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K : Subgroup G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) S9.isL3char2 →
    Nat.card (Subgroup.center (PQuot 3 K)) = 3 →
    ∃ E T : Subgroup G, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ T ≤ K ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set G) ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K

structure Lemma105MoreInputs (G : Type) [Group G] [Finite G] : Prop where
  i91type : I91TypeAt G
  excfield : ExcNoFieldAt G
  autl3 : AutL3At G
  sl3tor : SL3TorusAt G

end CFSG.LocalAnalysis.GLTheoremA
