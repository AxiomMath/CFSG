module

public import CFSG.ClassicalInvolution.SmallCases.DSplitBridge
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedInputs

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable (p f : ℕ) [Fact p.Prime]

structure DBranchD {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  below : CITBelowU p f (Nat.card G)
  member : IsClassicalMember p f K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  dDisconnected : ¬ DConnected (CoreAssembly.conjClass K)

variable {p f}

theorem DBranchD.toDBranch {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (h : DBranchD p f K z) : DBranch p f K z where
  nonabelian := h.nonabelian
  odd := h.odd
  five := h.five
  below := h.below
  member := h.member
  rank := h.rank
  notFourGenerated := h.notFourGenerated
  disconnected := fun hΔ => h.dDisconnected (dConnected_of_deltaConnected hΔ)

variable (p f)

structure TightBranchD {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  branch : DBranchD p f K z
  control : ControlC K
  edgeless : DEdgeless (CoreAssembly.conjClass K)

theorem TightBranchD.toTightBranch {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (h : TightBranchD p f K z) : TightBranch p f K z :=
  ⟨h.branch.toDBranch, h.control, deltaEdgeless_of_dEdgeless h.edgeless⟩

@[expose] def TightCSMD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranchD p f K z → CommutingSylowForcesCommuting K

@[expose] def TightE2D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranchD p f K z → CentralizerTwoRankOne K

@[expose] def TightE3D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranchD p f K z → NormalizerQuotientTwoGenerated K

@[expose] def TightControlledD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    TightBranchD p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def ControlledWithEdgeD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ControlC K → ¬ DEdgeless (CoreAssembly.conjClass K) →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

@[expose] def UncontrolledDatumD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ¬ ControlC K → ConnectedA2.HasDatum p f K

@[expose] def UncontrolledFromDatumD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ¬ ControlC K → ConnectedA2.HasDatum p f K →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

structure DisconnectedInputsD : Prop where
  tight : TightControlledD p f
  edges : ControlledWithEdgeD p f
  datum : UncontrolledDatumD p f
  fromDatum : UncontrolledFromDatumD p f

@[expose] def SmallDisconnectedD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

variable {p f}

theorem tightControlledD_of_sylow (hcsm : TightCSMD p f) (he2 : TightE2D p f)
    (he3 : TightE3D p f) : TightControlledD p f := by
  intro G _ _ _ K z ht
  exact absurd (twoSubgroupsFourGenerated_of_edgeless ht.branch.odd ht.branch.five
    ht.branch.member ht.control (deltaEdgeless_of_dEdgeless ht.edgeless) (hcsm G K z ht)
    (he2 G K z ht) (he3 G K z ht)) ht.branch.notFourGenerated

theorem tightCSMD_of_tightCSM (h : TightCSM p f) : TightCSMD p f :=
  fun G _ _ _ K z ht => h G K z ht.toTightBranch

theorem tightE2D_of_tightE2 (h : TightE2 p f) : TightE2D p f :=
  fun G _ _ _ K z ht => h G K z ht.toTightBranch

theorem tightE3D_of_tightE3 (h : TightE3 p f) : TightE3D p f :=
  fun G _ _ _ K z ht => h G K z ht.toTightBranch

theorem tightControlledD_of_tightControlled (h : TightControlled p f) : TightControlledD p f :=
  fun G _ _ _ K z ht => h G K z ht.toTightBranch

theorem uncontrolledDatumD_of_uncontrolledDatum (h : UncontrolledDatum p f) :
    UncontrolledDatumD p f :=
  fun G _ _ _ K z hb hC => h G K z hb.toDBranch hC

theorem uncontrolledFromDatumD_of_uncontrolledFromDatum (h : UncontrolledFromDatum p f) :
    UncontrolledFromDatumD p f :=
  fun G _ _ _ K z hb hC hd => h G K z hb.toDBranch hC hd

theorem smallDisconnectedD_of_inputsD (h : DisconnectedInputsD p f) : SmallDisconnectedD p f := by
  intro G _ _ _ K z hb
  by_cases hC : ControlC K
  · by_cases hE : DEdgeless (CoreAssembly.conjClass K)
    · exact h.tight G K z ⟨hb, hC, hE⟩
    · exact h.edges G K z hb hC hE
  · exact h.fromDatum G K z hb hC (h.datum G K z hb hC)

theorem smallDisconnected_of_dSplit (hb : DBridge p f) (hd : DisconnectedInputsD p f) :
    SmallDisconnected p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ
  by_cases hD : DConnected (CoreAssembly.conjClass K)
  · exact absurd (hb G hnab hp2 hq hBelow K z hz h3 h4 hD) hΔ
  · exact smallDisconnectedD_of_inputsD hd G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hD⟩

end CFSG.ClassicalInvolution.Disconnected
