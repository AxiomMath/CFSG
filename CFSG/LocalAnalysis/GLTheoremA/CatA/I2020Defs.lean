module

public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

@[expose] def I2020FixCentAt {X : Type} [Group X] (β : MulAut X) (J : Subgroup X) : Prop :=
  ∀ T : Subgroup X, CFSG.Open.fusionIsSylowIn 2 T J →
    ∀ S : Subgroup (MulAut X), IsPGroup 2 S → (∀ s ∈ S, ∀ t ∈ T, s t = t) →
      (∀ s ∈ S, β * s * β⁻¹ ∈ S) → ⁅S, Subgroup.zpowers β⁆ = S →
        ∀ s ∈ S, ∀ j ∈ J, s j = j

@[expose] def I2020FixCent (p : ℕ) {X : Type} [Group X] (P : Subgroup X → Prop)
    (β : MulAut X) : Prop :=
  ∀ J : Subgroup X, GLAPComponent p (fixSubgroup β) J → P J → I2020FixCentAt β J

@[expose] def I2020LinInner : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (F : Type) [Field F] [Finite F] [CharP F q], p ∣ Nat.card F - 1 →
      ∀ (n : ℕ), 3 ≤ n → n ≤ 4 → ∀ (A : GL (Fin n) F) (c : Fˣ),
        A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c →
        I2020FixCent p (fun _ => True) (LinearFlag.conjAut n F A)

@[expose] def I2020LinOuter : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (F : Type) [Field F] [Finite F] [CharP F q] (n : ℕ), 3 ≤ n → n ≤ 4 →
      ∀ β : MulAut (LinearFlag.projectiveSL n F), β ^ p = 1 →
        (∀ A : GL (Fin n) F, β ≠ LinearFlag.conjAut n F A) →
        I2020FixCent p (fun _ => True) β

@[expose] def I2020UniInner : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData q f K), p ∣ q ^ f + 1 →
      ∀ (n : ℕ), 3 ≤ n → n ≤ 4 → ∀ (A : primeFormUnitary h (idGram K n)) (c : Kˣ),
        (A : GL (Fin n) K) ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c →
        I2020FixCent p (fun _ => True) (primeFormConjHom h (idGram K n) A)

@[expose] def I2020UniOuter : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData q f K) (n : ℕ), 3 ≤ n → n ≤ 4 →
      ∀ β : MulAut (primeFormP h (idGram K n)), β ^ p = 1 →
        (∀ A : primeFormUnitary h (idGram K n), β ≠ primeFormConjHom h (idGram K n) A) →
        I2020FixCent p (fun _ => True) β

@[expose] def I2020OrthTag (t : StatedLieTag) (n : ℕ) : Prop :=
  t = .POmegaOdd ∧ n = 3 ∨ (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ n = 4

@[expose] def I2020OrthInner : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (t : StatedLieTag) (n : ℕ), I2020OrthTag t n →
      ∀ (G : Type) [Group G] [Finite G] (f : ℕ), StatedClassicalModel G t n q f →
        p ∣ (q ^ f) ^ 2 - 1 → ∀ a : G, a ^ p = 1 →
          I2020FixCent p (JType p q) (MulAut.conj a)

@[expose] def I2020OrthOuter : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (t : StatedLieTag) (n : ℕ), I2020OrthTag t n →
      ∀ (G : Type) [Group G] [Finite G] (f : ℕ), StatedClassicalModel G t n q f →
        (t = .POmegaPlus → p ≠ 3) →
        ∀ β : MulAut G, β ^ p = 1 → (∀ a : G, β ≠ MulAut.conj a) →
          I2020FixCent p (JType p q) β

@[expose] def I2020D4Three : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ 2 → q ≠ 3 →
    ∀ (G : Type) [Group G] [Finite G] (f : ℕ), StatedClassicalModel G .POmegaPlus 4 q f →
      ∀ β : MulAut G, β ^ 3 = 1 → (∀ a : G, β ≠ MulAut.conj a) →
        I2020FixCent 3 (JType 3 q) β

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
