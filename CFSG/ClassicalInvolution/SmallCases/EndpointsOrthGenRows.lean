module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternB

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinSp2Chain (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 2 .PSp 2 (conjClass K) z →
      ∃ (K₁ K₂ : Subgroup G) (z₁ : G), K₁ ∈ conjClass K ∧ K₂ ∈ conjClass K ∧
        IsClassicalMember p f K₁ z₁ ∧ Commutes K K₂ ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K K₁) ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K₁ K₂) ∧
        ∃ Λ : SpLayer p f 2 (conjClass K) z,
          locImg (conjClass K) z K₂ ≤ (Λ.D.hom Λ.i₁).range

theorem partnerPieceTwinSp2_of_chain (h : TwinSp2Chain p f) : PartnerPieceTwinSp2 p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, hK₂i⟩ := h G hnab K z S hshape
  exact ⟨K₁, hK₁, z₁, hz₁, p01, partnerPatternBPair_two S.odd S.five S.inClass S.p1 Λ
    (mem_conjClass_self K) hK₂ S.cls hz₁ c02 p01 p12 hK₂i⟩

theorem pieceTwinSp2_of_chain (h : TwinSp2Chain p f) : PieceTwinSp2 p f :=
  pieceTwinSp2_of_partner (partnerPieceTwinSp2_of_chain h)

end CFSG.ClassicalInvolution.Generic.CoreAssembly
