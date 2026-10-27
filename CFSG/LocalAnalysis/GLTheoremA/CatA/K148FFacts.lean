module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def K148FFieldAut (p : ℕ) (Q : Type) [Group Q] (φ : MulAut Q) : Prop :=
  GLAMarking Q fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (fun a b => φ a = b))

@[expose] def K148FG2CompFact : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (H : Subgroup C) (f : ℕ) (y : C),
    catalogIs ↥H (isG2n f) → y ∈ Subgroup.normalizer (H : Set C) → y ^ 3 = 1 →
    ∀ M : Subgroup C, GLAPComponent 3 (H ⊓ Subgroup.centralizer ({y} : Set C)) M →
      ∀ n : ℕ, catalogIs (PSimple 3 M) (isL2n n) → 2 ≤ f ∧ n = f

@[expose] def K148FTwoFact : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (q : TauCeti.PrimePower), q.p = 2 → q.exponent = 1 →
    catalogIs P (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q) → ∀ τ : MulAut P, τ ^ 3 = 1 →
      ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut τ →
      (∀ S S' : Subgroup P, GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ) S →
          GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ) S' → S = S') ∧
      (∀ S : Subgroup P, GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ) S → IsSimpleGroup ↥S) ∧
      (∀ c : P, c ^ 3 = 1 → τ c = c → ∀ S : Subgroup P,
          GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ) S → ∀ M : Subgroup P,
          GLAPComponent 3 (S ⊓ Subgroup.centralizer ({c} : Set P)) M →
          ∀ n : ℕ, ¬ catalogIs (PSimple 3 M) (isL2n n))

@[expose] def K148FLangFact : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (q : TauCeti.PrimePower), q.p = 2 →
    catalogIs P (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q) → ∀ τ : MulAut P, τ ^ 3 = 1 →
      ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut τ →
      ∀ S : Subgroup P, GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ) S → IsG2Quot 3 S →
        (2 ≤ q.exponent ∧ catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) (isG2n q.exponent)) ∨
        (q.exponent = 1 ∧ catalogIs (PQuot 3 S) isU33)

@[expose] def K148FC1LayerFact : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (q : TauCeti.PrimePower), q.p = 2 → 2 ≤ q.exponent →
    catalogIs P (CFSG.LocalAnalysis.GLTheoremA.I2023.isTD4Of q) → ∀ τ : MulAut P, τ ^ 3 = 1 →
      ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut τ →
      catalogIs ↥(CFSG.RankThree.PartTwo.Sec4.autFix τ) (isG2n q.exponent) →
      ∀ c : P, c ^ 3 = 1 → τ c = c →
      (∃ S : Subgroup P, GLAPComponent 3 (CFSG.RankThree.PartTwo.Sec4.autFix τ ⊓ Subgroup.centralizer ({c} : Set P)) S ∧
          catalogIs (PSimple 3 S) (isL2n q.exponent)) →
      ∃ M₀ : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({c} : Set P)) M₀ ∧
        (∀ M : Subgroup P, GLAPComponent 3 (Subgroup.centralizer ({c} : Set P)) M → M = M₀) ∧
        catalogIs (PSimple 3 M₀) (isL2n (3 * q.exponent)) ∧ (∀ m ∈ M₀, τ m ∈ M₀) ∧
        ∃ φ : MulAut (PQuot 3 M₀), φ ^ 3 = 1 ∧ ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut φ ∧
          (∀ m : M₀, ∃ m' : M₀, (m' : P) = τ⁻¹ m ∧ φ (QuotientGroup.mk m) = QuotientGroup.mk m') ∧
          K148FFieldAut 3 (PQuot 3 M₀) φ

end CFSG.LocalAnalysis.GLTheoremA

end
