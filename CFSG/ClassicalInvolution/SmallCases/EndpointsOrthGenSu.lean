module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthRows
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusFinal

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem SuLayer.exists_shortNode_odd {a : ℕ} (Λ : SuLayer p f a Ω x) [Finite G] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω) (hP1 : LocalOddCentral Ω {x}) {M : Subgroup G}
    (hM : M ∈ centralizingMembers Ω {x}) (hMi : locImg Ω x M ≤ (Λ.D.hom Λ.i₁).range) :
    ∃ Us : Subgroup G, Λ.IsShortNode (minusCoeffs_irr p f) M Us :=
  Λ.exists_shortNode hp2 hq hΩ hP1 (WeakCT.SU4.su4SpinMinus_galois hp2 hq)
    (spinMinus6Generated_galois hp2) (spinMinus6_noCover_galois hp2 hq) hM hMi

end CFSG.ClassicalInvolution.RouteD

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinSU4Chain (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∃ (K₁ K₂ : Subgroup G) (z₁ : G), K₁ ∈ conjClass K ∧ K₂ ∈ conjClass K ∧
        IsClassicalMember p f K₁ z₁ ∧ Commutes K K₂ ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) ∧
        ∃ Λ : SuLayer p f 2 (conjClass K) z, ∃ Us : Subgroup G,
          Λ.IsShortNode (minusCoeffs_irr p f) K₂ Us ∧ Us ≤ Subgroup.centralizer ({z₁} : Set G)

theorem partnerPieceTwinSU4_of_chain (h : TwinSU4Chain p f) : PartnerPieceTwinSU4 p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, Us, hsn, hUs⟩ := h G hnab K z S hshape
  exact ⟨K₁, hK₁, z₁, hz₁, p01, Λ.partnerPatternMinus_of_shortNode S.odd S.five S.inClass
    (mem_conjClass_self K) S.cls hK₂ c02 hsn hUs p12⟩

theorem pieceTwinSU4_of_chain (hb : SU4SpinMinus p f (minusCoeffs_irr p f))
    (hg6 : SpinMinus6Generated (minusCoeffs_irr p f)) (h : TwinSU4Chain p f) :
    PieceTwinSU4 p f :=
  pieceTwinSU4_of_partner hb hg6 (partnerPieceTwinSU4_of_chain h)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
