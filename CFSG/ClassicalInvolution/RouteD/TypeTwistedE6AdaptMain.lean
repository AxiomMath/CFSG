module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptVee
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerMain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplitProd
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {z : G}

@[expose] def AdaptedFrame (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f)
    (α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6) : Prop :=
  ∃ F : SU6Frame p f hf,
    F.R₁ = LcU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num)) ∧
      (∀ x ∈ F.S₂, α x = x) ∧ ∀ x ∈ F.S₃, α x = x

@[expose] def TE6AdaptedFrames (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (c : UCtx p f 5 Ω K z)
    (nd : UNodes c) : Prop :=
  ∀ N ∈ centralizingMembers Ω {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W N (nd.j 0)) →
    ∀ Θ : Su (GaloisField p (2 * f)) p f 6 →* G, TE6Chart c nd Θ →
    ∀ v : G, IsClassicalMember p f N v →
    ∀ α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6,
      (∀ x, Θ (α x) = v * Θ x * v⁻¹) → AdaptedFrame p f hf α

variable [Finite G]

theorem commutes_of_alpha_fixed (hMFZ : Gaps.FundNoncentral p)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeU p f 5 Ω z)
    {c : UCtx p f 5 Ω K z} {nd : UNodes c} {Θ : Su (GaloisField p (2 * f)) p f 6 →* G}
    (hΘ : TE6Chart c nd Θ) {N : Subgroup G} (hN : N ∈ Ω) {v : G} (hv : IsClassicalMember p f N v)
    (hNK : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K N)
    {α : Su (GaloisField p (2 * f)) p f 6 →* Su (GaloisField p (2 * f)) p f 6}
    (hα : ∀ x, Θ (α x) = v * Θ x * v⁻¹) {S : Subgroup (Su (GaloisField p (2 * f)) p f 6)}
    (hS : ⁅S, S⁆ = S) (hfix : ∀ x ∈ S, α x = x) : Commutes N (S.map Θ) := by
  classical
  have : NeZero f := ⟨by
    rintro rfl
    have := c.hq
    simp at this⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField c.hp2 c.hq
  obtain ⟨D, hD, -⟩ := hshape
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 :=
    ⟨D, by omega⟩
  refine commutes_partner_of_perfect_conj c.hp2 c.hq hMFZ hS3 c.hΩ hsingle c.hz hD4 c.hP1 hN
    hv hNK (S := S.map Θ) ?_ ?_ ?_
  · rw [← Subgroup.map_commutator, hS]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (TE6Chart.centralizes_of_fixed hα (hfix x hx)).symm
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact hΘ.commutes_K_range k hk (Θ x) ⟨x, rfl⟩

theorem te6Adaptation_of_adaptedFrames (hf : 1 ≤ f) (hMFZ : Gaps.FundNoncentral p)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hshape : LocalShapeU p f 5 Ω z)
    (c : UCtx p f 5 Ω K z) (nd : UNodes c) (hAF : TE6AdaptedFrames p f hf c nd) :
    TE6Adaptation hf nd := by
  classical
  have : NeZero f := ⟨by omega⟩
  intro N hN hNK hNj
  obtain ⟨v, hv⟩ := c.hΩ.classical N hN.1
  have hvz : v * z * v⁻¹ = z := partner_involution_commutes c.hp2 c.hz hv hNK
  have hv2 : v * v = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one v
    rwa [hv.orderOf_eq_two] at this
  obtain ⟨Θ, hΘ⟩ := c.exists_te6Chart nd
  obtain ⟨α, g, φ, hα, -⟩ := hΘ.exists_alpha hvz hv2
  obtain ⟨F, hF1, hFS2, hFS3⟩ := hAF N hN hNK hNj Θ hΘ v hv α hα
  have hcomm : ∀ S : Subgroup (Su (GaloisField p (2 * f)) p f 6), ⁅S, S⁆ = S →
      (∀ x ∈ S, α x = x) → Commutes N (S.map Θ) := fun S hS hfix =>
    commutes_of_alpha_fixed hMFZ hsingle hshape hΘ hN.1 hv hNK hα hS hfix
  have h4 : 4 ≤ Nat.card (GaloisField p (2 * f)) := by
    rw [c.card_eq]
    have := c.hq
    nlinarith
  obtain ⟨h12, h23⟩ := Gaps.map_blocks_perfect h4 F.ι₃
  rw [F.ι₃_B12] at h12
  rw [F.ι₃_B23] at h23
  refine ⟨![F.R₁.map Θ, F.S₂.map Θ, F.S₃.map Θ], hΘ.isTE6Base hf F, ?_, hcomm _ h23 hFS2,
    hcomm _ h12 hFS3⟩
  show F.R₁.map Θ = nd.j 0
  rw [hF1, ← range_blockEmb2_eq_LcU_nodePair c.h2 (by norm_num : 0 < 5)]
  exact hΘ.block ⟨0, by norm_num⟩

end CFSG.ClassicalInvolution.RouteD.NonClassical
