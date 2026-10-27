module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedSplit
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedEdgeless
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2Inputs

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable (p f : ℕ) [Fact p.Prime]

structure TightBranch {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranch p f K z
  control : ControlC K
  edgeless : DeltaEdgeless K

@[expose] def TightCSM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z → CommutingSylowForcesCommuting K

@[expose] def TightE2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z → CentralizerTwoRankOne K

@[expose] def TightE3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z → NormalizerQuotientTwoGenerated K

@[expose] def TightControlled : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranch p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def ControlledWithEdge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ControlC K → ¬ DeltaEdgeless K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def UncontrolledDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ¬ ControlC K → ConnectedA2.HasDatum p f K

@[expose] def UncontrolledFromDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranch p f K z → ¬ ControlC K → ConnectedA2.HasDatum p f K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

structure DisconnectedInputs : Prop where
  tight : TightControlled p f
  edges : ControlledWithEdge p f
  datum : UncontrolledDatum p f
  fromDatum : UncontrolledFromDatum p f

variable {p f}

theorem tightControlled_of_sylow (hcsm : TightCSM p f) (he2 : TightE2 p f) (he3 : TightE3 p f) :
    TightControlled p f := by
  intro G _ _ _ K z ht
  exact absurd (twoSubgroupsFourGenerated_of_edgeless ht.branch.odd ht.branch.five
    ht.branch.member ht.control ht.edgeless (hcsm G K z ht) (he2 G K z ht) (he3 G K z ht))
    ht.branch.notFourGenerated

theorem smallDisconnectedControlled_of_inputs (ht : TightControlled p f)
    (he : ControlledWithEdge p f) : SmallDisconnectedControlled p f := by
  intro G _ _ _ K z hb hC
  by_cases hE : DeltaEdgeless K
  · exact ht G K z ⟨hb, hC, hE⟩
  · exact he G K z hb hC hE

theorem smallDisconnectedUncontrolled_of_inputs (hd : UncontrolledDatum p f)
    (hr : UncontrolledFromDatum p f) : SmallDisconnectedUncontrolled p f := by
  intro G _ _ _ K z hb hC
  exact hr G K z hb hC (hd G K z hb hC)

theorem smallDisconnected_of_inputs (h : DisconnectedInputs p f) : SmallDisconnected p f :=
  smallDisconnected_of_split
    (smallDisconnectedControlled_of_inputs h.tight h.edges)
    (smallDisconnectedUncontrolled_of_inputs h.datum h.fromDatum)

end CFSG.ClassicalInvolution.Disconnected
