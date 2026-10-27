module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
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
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
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

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open

@[expose] def S2019SympInner (Qs : ℕ → Prop) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → Qs q →
    ∀ (G : Type) [Group G] (n f : ℕ), StatedClassicalModel G .PSp n q f →
      ∀ a : G, a ^ p = 1 → S2019FixCentralizes p (MulAut.conj a)

@[expose] def S2019SympOuter (Qs : ℕ → Prop) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → Qs q →
    ∀ (G : Type) [Group G] (n f : ℕ), StatedClassicalModel G .PSp n q f →
      ∀ β : MulAut G, β ^ p = 1 → (∀ a : G, β ≠ MulAut.conj a) → S2019FixCentralizes p β

@[expose] def S2019OrthInner (Qs : ℕ → Prop) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → Qs q →
    ∀ (t : StatedLieTag), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      ∀ (G : Type) [Group G] (n f : ℕ), StatedClassicalModel G t n q f →
        ∀ a : G, a ^ p = 1 → S2019FixCentralizes p (MulAut.conj a)

@[expose] def S2019OrthOuter (Qs : ℕ → Prop) : Prop :=
  ∀ (p q : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p → Qs q →
    ∀ (t : StatedLieTag), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      ∀ (G : Type) [Group G] (n f : ℕ), StatedClassicalModel G t n q f →
        (t = .POmegaPlus → n = 4 → p ≠ 3) →
        ∀ β : MulAut G, β ^ p = 1 → (∀ a : G, β ≠ MulAut.conj a) → S2019FixCentralizes p β

@[expose] def S2019OrthD4Outer : Prop :=
  ∀ (q : ℕ), q.Prime → q ≠ 2 → q ≠ 3 →
    ∀ (G : Type) [Group G] (f : ℕ), StatedClassicalModel G .POmegaPlus 4 q f →
      ∀ β : MulAut G, β ^ 3 = 1 → (∀ a : G, β ≠ MulAut.conj a) → S2019FixCentralizes 3 β

end CFSG.LocalAnalysis.GLTheoremA.S2019
