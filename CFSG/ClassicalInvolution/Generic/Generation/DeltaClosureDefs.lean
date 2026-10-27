module

public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn)

section Defs

variable {G : Type} [Group G]

@[expose] def rankThreeSpan (A : Subgroup G) : Subgroup G :=
  ⨆ E₀ ∈ signalizerFunctorEk 2 3 A, Subgroup.centralizer (E₀ : Set G)

abbrev LocalQuot (Ω : Set (Subgroup G)) (a : G) : Type :=
  ↥(centralizingLayer Ω {a}) ⧸ classicalInvolutionOddCore ↥(centralizingLayer Ω {a})

@[expose] def localFamily (Ω : Set (Subgroup G)) (a : G) : Set (Subgroup (LocalQuot Ω a)) :=
  oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a}))

@[expose] def OmegaConnected (Ω : Set (Subgroup G)) : Prop :=
  ∀ L ∈ Ω, ∀ L' ∈ Ω, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) L L'

variable (p f : ℕ) [Fact p.Prime]

@[expose] def SingleClassComponents {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) : Prop :=
  ∀ i, FundamentalSingleClass (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D

@[expose] def CentralizerGenerationModO (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) : Prop :=
  centralizingLayer Ω {a} ≤ oddCoreIn (centralizingLayer Ω {a}) ⊔
    ⨆ E₀ ∈ signalizerFunctorEk 2 3 A, (Subgroup.centralizer (E₀ : Set G) ⊓ centralizingLayer Ω {a})

@[expose] def FrameGenerationModO (Ω S : Set (Subgroup G)) (a : G) : Prop :=
  centralizingLayer Ω {a} ≤ oddCoreIn (centralizingLayer Ω {a}) ⊔
    ⨆ K ∈ S, ⨆ (_ : K ≤ Subgroup.centralizer ({a} : Set G)), K

@[expose] def FrameCoversModO (Ω S : Set (Subgroup G)) (a : G) : Prop :=
  ∀ L ∈ centralizingMembers Ω {a}, ∃ K ∈ S, K ≤ Subgroup.centralizer ({a} : Set G) ∧
    ∃ x ∈ L, ∃ y ∈ K, x * y * x⁻¹ * y⁻¹ ∉ oddCoreIn (centralizingLayer Ω {a})

structure LocalHypotheses (Ω : Set (Subgroup G)) (A : Subgroup G) : Prop where
  inClass : InClass p f Ω
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  noncentral : ∀ a ∈ A, a ≠ 1 → a ∉ Subgroup.center G
  lie : LocalLieSystems p f Ω
  single : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
    SingleClassComponents p f D

@[expose] def IsFrameInvolution (S : Set (Subgroup G)) (a : G) : Prop :=
  ∃ K ∈ S, IsClassicalMember p f K a

@[expose] def InvolutionLink (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop :=
  ∀ M ∈ centralizingMembers Ω {a}, ∀ z : G, IsClassicalMember p f M z →
    ∃ K ∈ S, ∃ z' ∈ A, IsClassicalMember p f K z' ∧
      ∃ h ∈ centralizingLayer Ω {a}, z = h * z' * h⁻¹

structure FrameSide (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) : Prop where
  elem : IsElemAbelian 2 A
  card : 16 ≤ Nat.card A
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z
  generation : ∀ a ∈ A, IsFrameInvolution p f S a → CentralizerGenerationModO Ω A a
  link : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a

@[expose] def omegaStar (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ rankThreeSpan A, ∃ K ∈ S, ∃ z ∈ A,
    IsClassicalMember p f K z ∧ IsClassicalMember p f L (h * z * h⁻¹)}

end Defs

end CFSG.ClassicalInvolution.Generic.DeltaClosure
