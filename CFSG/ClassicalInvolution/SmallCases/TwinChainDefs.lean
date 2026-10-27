module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthGenSu

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinSU4ChainData (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∃ (K₁ K₂ : Subgroup G) (z₁ : G), K₁ ∈ conjClass K ∧ K₂ ∈ conjClass K ∧
        IsClassicalMember p f K₁ z₁ ∧ Commutes K K₂ ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) ∧
        ∃ Λ : SuLayer p f 2 (conjClass K) z,
          locImg (conjClass K) z K₂ ≤ (Λ.D.hom Λ.i₁).range

@[expose] def SU4PatternStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∀ (Λ : SuLayer p f 2 (conjClass K) z) (K₁ K₂ : Subgroup G) (z₁ : G),
        K₁ ∈ conjClass K → K₂ ∈ conjClass K → IsClassicalMember p f K₁ z₁ →
        Commutes K K₂ →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁) →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) →
        locImg (conjClass K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∃ Us : Subgroup G, Λ.IsShortNode (minusCoeffs_irr p f) K₂ Us ∧
          Us ≤ Subgroup.centralizer ({z₁} : Set G)

theorem twinSU4Chain_of_chainData (hc : TwinSU4ChainData p f) (hp : SU4PatternStmt p f) :
    TwinSU4Chain p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, hK₂i⟩ := hc G hnab K z S hshape
  obtain ⟨Us, hsn, hUs⟩ := hp G hnab K z S hshape Λ K₁ K₂ z₁ hK₁ hK₂ hz₁ c02 p01 p12 hK₂i
  exact ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, Us, hsn, hUs⟩

theorem twinSU4ChainData_of_chain (h : TwinSU4Chain p f) : TwinSU4ChainData p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, Us, hsn, -⟩ := h G hnab K z S hshape
  refine ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, ?_⟩
  exact le_sup_left.trans hsn.2.2.2.2.2.le

@[expose] def ProductOfTwoP1 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LocalOddCentral (conjClass K) {z * w}

@[expose] def LinkedAtProduct {G : Type} [Group G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (z w : G) : Prop :=
  ∃ N ∈ centralizingMembers Ω {z * w}, N ≠ K ∧ ¬ Commutes K N

@[expose] def TwinSp2Linked (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSp 2 (conjClass K) z →
      ∀ (Λ : SpLayer p f 2 (conjClass K) z) (K₂ : Subgroup G),
        K₂ ∈ centralizingMembers (conjClass K) {z} →
        locImg (conjClass K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ w : G, IsClassicalMember p f K₂ w → LinkedAtProduct (conjClass K) K z w

@[expose] def TwinSU4Linked (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∀ (Λ : SuLayer p f 2 (conjClass K) z) (K₂ : Subgroup G),
        K₂ ∈ centralizingMembers (conjClass K) {z} →
        locImg (conjClass K) z K₂ ≤ (Λ.D.hom Λ.i₁).range →
        ∀ w : G, IsClassicalMember p f K₂ w → LinkedAtProduct (conjClass K) K z w

end CFSG.ClassicalInvolution.Generic.CoreAssembly
