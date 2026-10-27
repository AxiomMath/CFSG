module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def IsCentralIn {G : Type} [Group G] (r : ℕ) (z : G) (K : Subgroup G) : Prop :=
  z ∈ K ∧ ∃ P : Subgroup G, P ≤ K ∧ IsPGroup r P ∧ z ∈ P ∧ P ≤ Subgroup.centralizer ({z} : Set G) ∧
    ∀ Q : Subgroup G, P ≤ Q → Q ≤ K → IsPGroup r Q → Q = P

@[expose] def U48CentInvAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L A E T : Subgroup G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight →
    A ≤ Subgroup.normalizer (L : Set G) → IsElemAbelian 3 A → E ≤ A → E ≤ L → Nat.card E = 3 ^ 2 →
    T ≤ L → IsPGroup 2 T → ¬ T ≤ GLAPPrimeCoreOf 3 L → A ≤ Subgroup.normalizer (T : Set G) →
    ∃ z : G, z ^ 2 = 1 ∧ z ≠ 1 ∧ IsCentralIn 2 z L ∧ A ≤ Subgroup.centralizer ({z} : Set G)

@[expose] def U48CentInvFieldAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (b z : G), GLAPComponent 3 X L → catalogIs ↥L S9.isU4eight → FieldOn 3 b L →
    z ^ 2 = 1 → IsCentralIn 2 z L → z ∈ Subgroup.centralizer ({b} : Set G) →
    IsCentralIn 2 z (L ⊓ Subgroup.centralizer ({b} : Set G))

structure I307At (G : Type) [Group G] [Finite G] : Prop where
  one : ∀ (X K E : Subgroup G) (z : G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) S9.isU4two →
    Odd (Nat.card (GLAPPrimeCoreOf 3 K)) → IsCentralIn 2 z K → z ^ 2 = 1 → z ≠ 1 →
    E ≤ K ⊓ Subgroup.centralizer ({z} : Set G) →
    IsElemAbelian 3 E → Nat.card E = 3 ^ 2 → ∃ y ∈ E, y ≠ 1 ∧ IsCentralIn 3 y K
  two : ∀ (X L : Subgroup G) (b y : G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isU4eight → FieldOn 3 b L →
    b ^ 3 = 1 → IsCentralIn 3 y (Ipart 3 L b) → IsCentralIn 3 y L

@[expose] def U48Cent3At (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X L : Subgroup G) (y : G), GLAPComponent 3 X L → catalogIs (PSimple 3 L) S9.isU4eight → y ^ 3 = 1 → y ≠ 1 →
    IsCentralIn 3 y L →
    GLAPComponent 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G))) ∧
      catalogIs (PSimple 3 (GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G)))) S9.isU3eight

@[expose] def I2811TAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X K E : Subgroup G) (z : G), GLAPComponent 3 X K → catalogIs (PSimple 3 K) S9.isU4two →
    Odd (Nat.card (GLAPPrimeCoreOf 3 K)) → IsCentralIn 2 z K → z ^ 2 = 1 → z ≠ 1 →
    E ≤ K ⊓ Subgroup.centralizer ({z} : Set G) →
    IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
    ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, E⁆ : Subgroup G) ≠ ⊥ ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ IsEmpty (T ≃* QuaternionGroup 2)

@[expose] def FieldAutPowClosedAt : Prop :=
  ∀ (lab : CFSG.Assembly.LargeEvenLabel), CFSG.Assembly.LargeEvenInLambda2 lab →
    ∀ Q : CFSG.Assembly.LargeEvenRawCont, CFSG.Assembly.LargeEvenRawDatum lab Q →
      CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F =>
        Q R I F ∧ ∀ f ∈ F, ∀ n : ℕ, 0 < n → f ^ n ∈ F

end CFSG.LocalAnalysis.GLTheoremA
