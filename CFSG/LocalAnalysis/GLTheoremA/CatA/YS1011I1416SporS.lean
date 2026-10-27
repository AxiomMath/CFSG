module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.PerfectAutomorphisms

@[expose] def I1416TwoSporS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ K : Subgroup S,
      GLAPComponent p (fixSubgroup β) K → IsChevSimple 2 (PSimple p K) →
      p ^ 2 ∣ Nat.card (MulAut (PSimple p K)) →
      ¬ (p = 3 ∧ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd (PSimple p K)) →
      p = 3 ∧ catalogIs (PSimple 3 K) (fun i => S10.isA6 i ∨ isA8 i ∨ isG2der i ∨ S9.isU4two i)

end CFSG.LocalAnalysis.GLTheoremA
