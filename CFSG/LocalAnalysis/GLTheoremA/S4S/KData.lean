module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def KD1912Chev (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsChevSimple p S → ∀ A : Subgroup (MulAut S), IsElemAbelian p A →
      IsTwoPrimaryWeaklyLocallyBalanced p 1 A ∨
        (p = 3 ∧ catalogIs S (onLie (isL2 27)) ∧ ¬ A ≤ innerAut S)

@[expose] def KD1912Two (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    catalogIs S (k2 p) → ∀ A : Subgroup (MulAut S), IsElemAbelian p A →
      IsTwoPrimaryWeaklyLocallyBalanced p 1 A

@[expose] def KD1913 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S isSmallThree → ∀ H : Subgroup (MulAut S),
    innerAut S ≤ H → ∀ x ∈ H, orderOf x = 3 →
      Nat.card (GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ≤ 4

@[expose] def KD2027 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → catalogIs S (onLie k3Lie) →
    ∀ A T : Subgroup (MulAut S), IsPGroup 3 A → IsPGroup 2 T →
      A ≤ Subgroup.normalizer (T : Set (MulAut S)) → (⁅A, T⁆ : Subgroup (MulAut S)) = T →
      (⁅A, (⁅T, T⁆ : Subgroup (MulAut S))⁆ : Subgroup (MulAut S)) = ⊥

@[expose] def KD264 (p : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → K ⊔ B = ⊤ → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥) ∨
      (p = 3 ∧ Nat.card B = 3 ^ 4 ∧ Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) = 3 ∧
        catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie isTrialityD4Big) ∧
        ∃ b ∈ B, ¬ InducesInnerMod 3 K b)

@[expose] def KD91 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (onLie isTrialityD4Big) →
    (∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
        IsPGroup 3 (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
        Subgroup.center E = ⊥) ∧
    (∀ β : MulAut S, β ^ 3 = 1 → β ∉ innerAut S → ∃ g : S,
      (MulAut.conj g * β) ^ 3 = 1 ∧ catalogIs ↥(fixSubgroup (MulAut.conj g * β)) (onLie isG2Big)) ∧
    (∀ (T : Type) [Group T] [Finite T], catalogIs T (onLie isG2Big) →
      IsSimpleGroup T ∧ (∃ a b : T, a * b ≠ b * a) ∧ 3 ∣ Nat.card T)

@[expose] def KD147 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S (onLie isG2Big) →
    (∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
        IsPGroup 3 (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
        Subgroup.center E = ⊥) ∧
    (∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 9) ∧
    ∀ z : S, orderOf z = 3 → GLAPLayer 3 (Subgroup.centralizer ({z} : Set S)) ≠ ⊥

@[expose] def KDM12 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S isM12 →
    (∀ (E : Type) [Group E] [Finite E], CFSG.Open.IsQuasisimple E →
        IsPGroup 3 (Subgroup.center E) → Nonempty ((E ⧸ Subgroup.center E) ≃* S) →
        Subgroup.center E = ⊥) ∧
    (∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D ≤ 9) ∧
    ∃ D U : Subgroup S, IsElemAbelian 3 D ∧ Nat.card D = 9 ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      D ≤ Subgroup.normalizer (U : Set S)

@[expose] def KD1426Cat : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    GLAPPrimeCore 3 ↥K = ⊥ → fullCoverLevel 3 ↥K = 3 →
    IsElemAbelian 3 B → K ⊔ B = ⊤ → 3 ^ 4 ≤ Nat.card B → IsMaxRankIn 3 B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∀ E : Subgroup Y, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥) →
    (catalogIs (↥K ⧸ Subgroup.center ↥K) isM12 → ∃ U : Subgroup Y, U ≤ K ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Y)) →
    Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
      catalogIs (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)))) k3NoA10 ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer
          ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
      T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ IsElemAbelian 2 T ∧
      Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥

end CFSG.LocalAnalysis.GLTheoremA
