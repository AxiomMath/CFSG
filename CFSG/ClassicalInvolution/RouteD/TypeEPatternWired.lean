module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternRows
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD edgeE)
open CFSG.LieType.CurtisTits (rankOne)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

@[expose] def E7TorusFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .POmegaPlus 6 (𝒞 K) z →
      ∀ c : ETCtx p f .POmegaPlus 6 (𝒞 K) K z, ∀ j : Fin 6 → Subgroup G,
        NodeSystem p f (edgeD 6) (𝒞 K) K z j →
        (∀ a, locImg (𝒞 K) z (j a) =
          (rankOne (modelUniv .POmegaPlus 6 p f Fact.out).D.rootGroup a).map c.d.ψ) →
        ∀ β ∈ 𝒞 K, ∀ t : G, IsClassicalMember p f β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
          Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z,
            TorusFixedP (by norm_num : 3 ≤ 6) c ((0 : Fin 6) : Fin (modelUniv .POmegaPlus 6 p f
              Fact.out).D.rank) ht

@[expose] def E7AttachmentsExcluded (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .POmegaPlus 6 (𝒞 K) z →
      ∀ j : Fin 6 → Subgroup G, NodeSystem p f (edgeD 6) (𝒞 K) K z j →
        ∀ β ∈ 𝒞 K, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ p₀ : Fin 6, (∀ a, a ≠ p₀ → Commutes β (j a)) →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j p₀)) →
          p₀ = 4 ∨ p₀ = 5

@[expose] def E8TorusFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .E7 0 (𝒞 K) z →
      ∀ c : ETCtx p f .E7 0 (𝒞 K) K z, ∀ j : Fin 7 → Subgroup G,
        NodeSystem p f (edgeE 7) (𝒞 K) K z j →
        (∀ a, locImg (𝒞 K) z (j a) =
          (rankOne (modelUniv .E7 0 p f Fact.out).D.rootGroup a).map c.d.ψ) →
        ∀ β ∈ 𝒞 K, ∀ t : G, IsClassicalMember p f β t →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
          Commutes β (j 0) → ∀ ht : t * z * t⁻¹ = z, TorusFixedE7 c ht

@[expose] def E8AttachmentsExcluded (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      LocalShapeT p f 1 .E7 0 (𝒞 K) z →
      ∀ j : Fin 7 → Subgroup G, NodeSystem p f (edgeE 7) (𝒞 K) K z j →
        ∀ β ∈ 𝒞 K, (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β) →
        ∀ p₀ : Fin 7, (∀ a, a ≠ p₀ → Commutes β (j a)) →
          (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W β (j p₀)) → p₀ = 6

@[expose] def E7SignPerp (p f : ℕ) [Fact p.Prime] : Prop :=
  SignPerp (fundamentalSubgroups .E7 (modelUniv .E7 0 p f Fact.out).D) (GaloisField p f)

theorem e7PartnerExists_of_inputs (hMFZ : Gaps.FundNoncentral p) (hT : E7TorusFixed p f)
    (hX : E7AttachmentsExcluded p f) : E7PartnerExists p f := by
  intro G _ _ _ hnab K z S hS
  exact exists_partnerAt_E7 hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    (single_class K) S.cls hS S.p1 (hT G hnab K z S hS) (hX G hnab K z S hS)

theorem e8PartnerExists_of_inputs (hMFZ : Gaps.FundNoncentral p) (hG : E7SignPerp p f)
    (hT : E8TorusFixed p f) (hX : E8AttachmentsExcluded p f) : E8PartnerExists p f := by
  intro G _ _ _ hnab K z S hS
  exact exists_partnerAt_E8 hMFZ S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    (single_class K) S.cls hS S.p1 (TypeEPattern.layerGeom_E7_of_signPerp S.five hG)
    (hT G hnab K z S hS) (hX G hnab K z S hS)

end CFSG.ClassicalInvolution.MilestoneAssembly
