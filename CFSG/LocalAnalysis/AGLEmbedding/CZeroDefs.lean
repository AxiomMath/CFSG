module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def IsSymThreeOrSUThreeTwo (Q : Type) [Group Q] : Prop :=
  Nonempty (Q ≃* Equiv.Perm (Fin 3)) ∨
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧ Nonempty (Q ≃* ↥(StatedSU 3 2 K))

structure IsCZeroMember (X I : Subgroup G) : Prop where
  le : I ≤ X
  subnormal : IsSubnormal I X
  shape : IsTwoPrimeComponent I I ∨
    (pCoreOf 2 I = pCoreOf 2 X ∧ IsSymThreeOrSUThreeTwo (↥I ⧸ CFSG.pCore 2 ↥I))

@[expose] def cZero (X : Subgroup G) : Set (Subgroup G) := {I | IsCZeroMember X I}

@[expose] def jZero (H L : Subgroup G) : Subgroup G := ⨆ I ∈ cZero (H ⊓ L), I

@[expose] def jOne (H L : Subgroup G) : Subgroup G :=
  ⨆ I ∈ cZero (H ⊓ L), CFSG.ComponentClassification.AS76b.oUpperTwo I

end CFSG.AGLEmbedding
