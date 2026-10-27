module

public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Thm6D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → DEdgeless (CoreAssembly.conjClass K) → ConclusionD G

@[expose] def Thm6EmptyD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → DEdgeless (CoreAssembly.conjClass K) → False

@[expose] def Thm7D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ¬ DEdgeless (CoreAssembly.conjClass K) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass K) K, K' ≠ K) → ConclusionD G

@[expose] def Thm8D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → ¬ DEdgeless (CoreAssembly.conjClass K) →
      (∀ K' ∈ twinSet (CoreAssembly.conjClass K) K, K' = K) → False

@[expose] def EdgelessControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchD p f K z → DEdgeless (CoreAssembly.conjClass K) → ControlC K

variable {p f}

theorem smallDisconnectedD_of_aschbacher (h6 : Thm6D p f) (h7 : Thm7D p f) (h8 : Thm8D p f) :
    SmallDisconnectedD p f := by
  intro G _ _ _ K z hb
  by_cases hE : DEdgeless (CoreAssembly.conjClass K)
  · exact h6 G K z hb hE
  · by_cases hT : ∃ K' ∈ twinSet (CoreAssembly.conjClass K) K, K' ≠ K
    · exact h7 G K z hb hE hT
    · exact (h8 G K z hb hE fun K' hK' => by_contra fun hne => hT ⟨K', hK', hne⟩).elim

theorem smallDisconnectedD_of_aschbacher_empty (h6 : Thm6EmptyD p f) (h7 : Thm7D p f)
    (h8 : Thm8D p f) : SmallDisconnectedD p f :=
  smallDisconnectedD_of_aschbacher (fun G _ _ _ K z hb hE => (h6 G K z hb hE).elim) h7 h8

theorem smallDisconnected_of_dBridge (hb : DBridge p f) (hs : SmallDisconnectedD p f) :
    CoreAssembly.SmallDisconnected p f := by
  intro G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ
  by_cases hD : DConnected (CoreAssembly.conjClass K)
  · exact absurd (hb G hnab hp2 hq hBelow K z hz h3 h4 hD) hΔ
  · exact hs G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hD⟩

theorem smallDisconnected_of_aschbacher (hb : DBridge p f) (h6 : Thm6D p f) (h7 : Thm7D p f)
    (h8 : Thm8D p f) : CoreAssembly.SmallDisconnected p f :=
  smallDisconnected_of_dBridge hb (smallDisconnectedD_of_aschbacher h6 h7 h8)

theorem tightControlledD_of_thm6D (h : Thm6D p f) : TightControlledD p f :=
  fun G _ _ _ K z ht => h G K z ht.branch ht.edgeless

theorem thm6D_of_tightControlledD (hC : EdgelessControl p f) (h : TightControlledD p f) :
    Thm6D p f :=
  fun G _ _ _ K z hb hE => h G K z ⟨hb, hC G K z hb hE, hE⟩

theorem controlledWithEdgeD_of_thm7D_thm8D (h7 : Thm7D p f) (h8 : Thm8D p f) :
    ControlledWithEdgeD p f := by
  intro G _ _ _ K z hb _ hE
  by_cases hT : ∃ K' ∈ twinSet (CoreAssembly.conjClass K) K, K' ≠ K
  · exact h7 G K z hb hE hT
  · exact (h8 G K z hb hE fun K' hK' => by_contra fun hne => hT ⟨K', hK', hne⟩).elim

theorem uncontrolledFromDatumD_of_smallDisconnectedD (h : SmallDisconnectedD p f) :
    UncontrolledFromDatumD p f :=
  fun G _ _ _ K z hb _ _ => h G K z hb

theorem thm6D_of_thm6A (hs : AscStandOfBranch p f) (h : Thm6A p f) : Thm6D p f :=
  fun G _ _ _ K z hb hE => (h G _ K (hs G K z hb) hE).conclusionD hb.notFourGenerated

theorem thm7D_of_thm7A (hs : AscStandOfBranch p f) (h : Thm7A p f) : Thm7D p f :=
  fun G _ _ _ K z hb _ hT =>
    (h G _ K (hs G K z hb) hT hb.dDisconnected).conclusionD hb.notFourGenerated

theorem thm8D_of_thm8A (hs : AscStandOfBranch p f) (h : Thm8A p f) : Thm8D p f :=
  fun G _ _ _ K z hb hE hT => h G _ K (hs G K z hb) hE hT hb.dDisconnected

theorem smallDisconnectedD_of_inputs (hΩ : HypOmegaModD p f) (hA : AEmptyD p f) (hall : IHAllD p f)
    (hih : IHInterface8 p) (h6 : Thm6A p f) (h7 : Thm7A p f) (h8 : Thm8A p f) :
    SmallDisconnectedD p f :=
  have hs := ascStandOfBranch_of hΩ hA hall hih
  smallDisconnectedD_of_aschbacher (thm6D_of_thm6A hs h6) (thm7D_of_thm7A hs h7)
    (thm8D_of_thm8A hs h8)

end CFSG.ClassicalInvolution.Disconnected
