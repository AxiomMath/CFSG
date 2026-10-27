module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def SporAltNoCompK (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    (s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → IsAltPType 3 J m → False

@[expose] def I1415SporSK : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    (s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent p (fixSubgroup β) J → ∀ m : ℕ, 10 ≤ m →
      Nonempty (PSimple p J ≃* alternatingGroup (Fin m)) → False

@[expose] def I1415NineSporSK : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    (s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B)) →
    (s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (fixSubgroup β) J → Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 9)) →
      s = TauCeti.SporadicName.HN ∨ s = TauCeti.SporadicName.Co1

@[expose] def I1415SevenSporSK : Prop := SporAltNoCompK 7

@[expose] def I1422SporSK : Prop := SporAltNoCompK 8

end CFSG.LocalAnalysis.GLTheoremA
