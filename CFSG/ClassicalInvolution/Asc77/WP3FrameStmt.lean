module

public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51
public import CFSG.ClassicalInvolution.Asc77.WP3LayerPair

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer

section Star

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def CentralizerGenerationStar (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) : Prop :=
  exactLayer Ω a ≤ oddCoreIn (exactLayer Ω a) ⊔
    ⨆ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω a)

@[expose] def InvolutionLinkStar (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G))
    (a : G) : Prop :=
  ∀ N ∈ Ω, ∀ z : G, IsClassicalMember p f N z →
    (ActsTrivOnQuot N a ∨ ∃ L ∈ Ω, IsClassicalMember p f L a ∧ ActsTrivOnQuot L z) →
    ∃ K ∈ S, ∃ z' ∈ A, IsClassicalMember p f K z' ∧ ∃ h ∈ exactLayer Ω a, z = h * z' * h⁻¹

structure FrameSideTwoStar (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Prop where
  elem : IsElemAbelian 2 A
  card : 8 ≤ Nat.card A
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z
  generation : ∀ a ∈ A, IsFrameInvolution p f S a → CentralizerGenerationStar Ω A a
  link : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLinkStar p f Ω A S a

structure FuzzyFrameDataStar (Ω : Set (Subgroup G)) (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G)
    (S : Set (Subgroup G)) (a : G) : Prop where
  mem : L₀ ∈ Ω
  cls : IsClassicalMember p f L₀ z₀
  z₀A : z₀ ∈ A
  tq : A ≤ trivialOnQuot L₀
  frame : FrameSideTwoStar p f Ω A S
  aA : a ∈ A
  a1 : a ≠ 1
  aClassical : ∃ M ∈ Ω, IsClassicalMember p f M a
  cover : ∀ K ∈ centMembers Ω a, ¬ IsClassicalMember p f K a →
    ∃ g : G, a ∈ conjSub g A ∧ InCommonComponent a K (conjSub g L₀)
  nine : p ^ f = 9 → ∃ x ∈ A, x ≠ 1 ∧ (∀ K ∈ centMembers Ω x, ∃ g : G, x ∈ conjSub g A ∧
    InCommonComponent x K (conjSub g L₀)) ∧ LocalLeviComponent p f Ω x

abbrev ShapePred : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Prop

variable {p f}

@[expose] def FrameExistsOn (p f : ℕ) [Fact p.Prime] (P : ShapePred) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → DConnected (CoreAssembly.conjClass K) → P G K z →
      ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
        FuzzyFrameDataStar p f (CoreAssembly.conjClass K) L₀ z₀ A S a ∧ Hyp51 A

@[expose] def FrameExistsStar (p f : ℕ) [Fact p.Prime] : Prop :=
  FrameExistsOn p f fun _ _ _ _ _ => True

end Star

section Chain

variable (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G]

@[expose] def ChainShape (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z,
    D.card = 2 ∧ ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧
      (D.tag i₁ = .PSL ∨ D.tag i₁ = .PSU) ∧ (D.rank i₁ = 3 ∨ D.rank i₁ = 4)

@[expose] def FrameVertex.ToralOnComponent (c : G) (B : Subgroup G) {K : Type} [Group K]
    (ψ : K →* OddQuot c) : Prop :=
  ∃ P : Subgroup K, (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
    ∀ b ∈ B, ∀ hb : b ∈ Subgroup.centralizer ({c} : Set G), ∃ x ∈ P, x * x = 1 ∧
      ∀ y ∈ ψ.range,
        oddQuotMk c ⟨b, hb⟩ * y * (oddQuotMk c ⟨b, hb⟩)⁻¹ = ψ x * y * (ψ x)⁻¹

@[expose] def ChainToral {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (z t z' : G) : Prop :=
  ∃ D : LocalLieSystemAt p f (exactFamily Ω z) z, ∀ j : Fin D.card,
    MovedByAll (Subgroup.closure ({z, t, z'} : Set G)) z
        (secComponentHom (normalizesLayer_exactFamily hΩ) D j).range →
      (D.tag j = .PSL ∨ D.tag j = .PSU) ∧
        FrameVertex.ToralOnComponent z (Subgroup.closure ({z, t, z'} : Set G))
          (secComponentHom (normalizesLayer_exactFamily hΩ) D j)

variable {p f}

structure ChainFrameData (Ω : Set (Subgroup G)) (K J K' : Subgroup G) (z t z' : G) : Prop where
  mem : K ∈ Ω
  hz : IsUniqueInvolution K z
  hJ : J ∈ omegaNbr Ω K
  ht : IsUniqueInvolution J t
  hK' : K' ∈ omegaNbr Ω K
  hz' : IsUniqueInvolution K' z'
  htz' : t * z' = z' * t
  hperp : K' ∉ KPerp Ω J

structure ChainFrameSymm (z t z' : G) : Prop where
  swap : ∀ e ∈ ({z', t * z'} : Set G), ∃ n ∈ Subgroup.normalizer
    ((Subgroup.closure ({z, t, z'} : Set G) : Subgroup G) : Set G),
    n * z * n⁻¹ = z ∧ n * t * n⁻¹ = e

variable (p f)

structure ChainFrameSetting (Ω : Set (Subgroup G)) (K J K' : Subgroup G) (z t z' : G) : Prop where
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  hyp : HypOmegaMod p f Ω
  aEmpty : ∀ M ∈ Ω, AEmpty Ω M
  noTwins : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M
  trans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M
  below : CITBelowU p f (Nat.card G)
  shape : ChainShape p f Ω z
  frame : ChainFrameData Ω K J K' z t z'
  symm : ChainFrameSymm z t z'
  toral : ChainToral p f hyp.conjInvariant z t z'

@[expose] def ChainFrameHyp51z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) z

@[expose] def ChainFrameHyp51t : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) t

@[expose] def ChainFrameHyp51zt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t)

@[expose] def ChainFrameHyp51 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K J K' : Subgroup G) (z t z' : G), ChainFrameSetting p f Ω K J K' z t z' →
      Hyp51 (Subgroup.closure ({z, t, z'} : Set G))

end Chain

end CFSG.ClassicalInvolution.Asc77
