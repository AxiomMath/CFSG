module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticE6
public import CFSG.ClassicalInvolution.Balance.LayerGenerationHybrid
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinPlus
public import CFSG.ClassicalInvolution.Generic.TypeCSmallRecognitionProof
public import CFSG.ClassicalInvolution.MilestoneAssemblyWired4
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalAll
public import CFSG.ClassicalInvolution.Q3.Remaining
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted
public import CFSG.ClassicalInvolution.RouteD.GapsToralB
public import CFSG.ClassicalInvolution.RouteD.GapsToralDSmall
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
public import CFSG.ClassicalInvolution.RouteD.TwinTenNodes
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternExclWired
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternWired
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpTable
public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsKG2Dichotomy
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedInputs
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthGenRows
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthGenSu
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
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
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
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
public import Certificates.Certificate2193
public import Certificates.Certificate2194
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2200
public import Certificates.Certificate2202
public import Certificates.Certificate2204
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate10019
public import Certificates.Certificate3085
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3157
public import Certificates.Certificate3169
public import Certificates.Certificate3170
public import Certificates.Certificate8046
public import Certificates.Certificate8052
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate9308
public import Certificates.Certificate9309
public import Certificates.Certificate9310
public import Certificates.Certificate9311
public import Certificates.Certificate9312
public import Certificates.Certificate9313
public import Certificates.Certificate9314
public import Certificates.Certificate9300
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBoot
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

@[expose] def LayerGenerationHybridRest (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), t ≠ .PSL → t ≠ .PSp → t ≠ .PSU → t ≠ .POmegaPlus →
    IsFundTag t → StatedLieAdmissible t n p e → p ≠ 2 → 5 ≤ p ^ e →
      Balance.Bootstrap.LayerGenerationPairOr p t n e

theorem LayerGenerationHybridRest.toHybrid (h : LayerGenerationHybridRest p) :
    Balance.Bootstrap.LayerGenerationHybrid p := by
  intro t n e hfund hadm hp2 hq
  by_cases hl : t = .PSL
  · subst hl
    exact Or.inr ⟨by decide, by decide, ModelFacts.commutingFundamentalGeneration_psl hp2 hadm⟩
  by_cases hs : t = .PSp
  · subst hs
    exact Or.inr ⟨by decide, by decide, ModelFacts.commutingFundamentalGeneration_psp hp2 hq hadm⟩
  by_cases hu : t = .PSU
  · subst hu
    exact Or.inr ⟨by decide, by decide, ModelFacts.commutingFundamentalGeneration_psu hp2 hadm⟩
  by_cases hd : t = .POmegaPlus
  · subst hd
    exact Or.inr ⟨by decide, by decide,
      Balance.Bootstrap.commutingFundamentalGeneration_pOmegaPlus hp2 hq hadm⟩
  exact h t n e hl hs hu hd hfund hadm hp2 hq

theorem LayerGenerationHybridRest.of_model (h : Balance.LayerGenerationModel) :
    LayerGenerationHybridRest p := fun t n e _ _ _ _ hfund hadm hp2 hq =>
  Or.inl (Balance.Bootstrap.layerGenerationPair_of_model h t n p e Fact.out hfund hadm hp2 hq)

@[expose] def ExoticLeviBlockG2D4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), InClass p f Ω → ∀ x : G,
    LocalOddCentral Ω {x} → p ^ f = 9 →
    ∀ D : LieSystemData p f (locQuot Ω x) (locFamily Ω x), ∀ i : Fin D.card,
      (D.tag i = .G2 ∨ D.tag i = .trialityD4) →
      ∃ L ∈ centralizingMembers Ω {x}, Balance.LeviBlockImage p f (locImg Ω x L)

theorem exoticLeviBlock_of_g2d4 (h : ExoticLeviBlockG2D4 p f) :
    Balance.Bootstrap.ExoticLeviBlock p f := by
  intro G _ _ Ω hΩ x hx h9 D i hi
  rcases hi with hi | hi | hi
  · exact h G Ω hΩ x hx h9 D i (Or.inl hi)
  · exact Balance.exists_member_leviBlockImage_of_twistedE6 (by rw [h9]; norm_num) D i hi
  · exact h G Ω hΩ x hx h9 D i (Or.inr hi)

@[expose] def TwinDTorusFixed₅ (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (m : ℕ) (_ : 5 ≤ m) (_ : m ≠ 6),
      LocalShapeT p f 2 .POmegaPlus m (𝒞 K) z →
      ∃ c : TCtx p f .POmegaPlus m (𝒞 K) K z, ∀ β ∈ 𝒞 K, ∀ t : G,
        ∀ ht : IsClassicalMember p f β t,
          ∀ hKβ : (∃ W, LinearBlockStandardPair (GaloisField p f) W K β),
            HasFixedMember (𝒞 K) K β z →
            Gaps.TorusFixedD (by omega : 3 ≤ m) c
              (partner_involution_commutes c.hp2 c.hz ht hKβ)

@[expose] def TwinDSmall₄₆ (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, m = 4 ∨ m = 6 →
      LocalShapeT p f 2 .POmegaPlus m (𝒞 K) z → ∀ β ∈ 𝒞 K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (𝒞 K) K β z → PartnerPatternD p f m (𝒞 K) K β t

theorem twinDPartnerPattern_of_parts₅ (hMFZ : Gaps.FundNoncentral p) (hT : TwinDTorusFixed₅ p f)
    (hS : TwinDSmall₄₆ p f) : TwinDPartnerPattern p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases h46 : m = 4 ∨ m = 6
  · exact hS G hnab K z S m h46 hshape β hβ t ht hKβ hfix
  obtain ⟨c, hc⟩ := hT G hnab K z S m (by omega) (by omega) hshape
  by_cases h7 : 7 ≤ m
  · exact Gaps.PartnerPatternD.of_torusFixed h7 hMFZ c (single_class K) hshape hβ ht hKβ hfix
      (hc β hβ t ht hKβ hfix)
  · obtain rfl : m = 5 := by omega
    exact Gaps.PartnerPatternD.of_torusFixed_five hMFZ c (single_class K) hshape hβ ht hKβ hfix
      (hc β hβ t ht hKβ hfix)

@[expose] def TwinBTorusFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (m : ℕ) (_ : 8 ≤ m),
      LocalShapeT p f 2 .POmegaOdd m (𝒞 K) z →
      ∃ c : TCtx p f .POmegaOdd m (𝒞 K) K z, ∀ β ∈ 𝒞 K, ∀ t : G,
        ∀ ht : IsClassicalMember p f β t,
          ∀ hKβ : (∃ W, LinearBlockStandardPair (GaloisField p f) W K β),
            HasFixedMember (𝒞 K) K β z →
            Gaps.TorusFixedB c (partner_involution_commutes c.hp2 c.hz ht hKβ) ∧
              ∀ (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
                (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2),
                Gaps.ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v →
                  Gaps.LastLongExcluded (p := p) (f := f) m v

@[expose] def TwinBSmallPattern (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 3 ≤ m → m ≤ 7 →
      LocalShapeT p f 2 .POmegaOdd m (𝒞 K) z → ∀ β ∈ 𝒞 K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (𝒞 K) K β z → PartnerPatternBPair p f m (𝒞 K) K β t

theorem twinBPartnerPattern_of_parts (hMFZ : Gaps.FundNoncentral p) (hT : TwinBTorusFixed p f)
    (hS : TwinBSmallPattern p f) : TwinBPartnerPattern p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases h8 : 8 ≤ m
  · obtain ⟨c, hc⟩ := hT G hnab K z S m h8 hshape
    obtain ⟨hfixed, hres⟩ := hc β hβ t ht hKβ hfix
    exact Gaps.PartnerPatternBPair.of_torusFixed h8 hMFZ c (single_class K) hshape hβ ht hKβ hfix
      hfixed hres
  · exact hS G hnab K z S m hm (by omega) hshape β hβ t ht hKβ hfix

@[expose] def SU6P1x (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 1 .PSU 6 (𝒞 K) z →
      ∀ (c : UCtx p f 5 (𝒞 K) K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
        ¬ Commutes β (nd.j 3) → LocalOddCentral (𝒞 K) {z * nd.w 0}

@[expose] def SU6NoG2D4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 1 .PSU 6 (𝒞 K) z →
      ∀ (c : UCtx p f 5 (𝒞 K) K z) (nd : UNodes c) {β : Subgroup G}, IsPartnerU c nd β →
        ¬ Commutes β (nd.j 3) →
        ∀ D : LieSystemData p f (locQuot (𝒞 K) (z * nd.w 0)) (locFamily (𝒞 K) (z * nd.w 0)),
          ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4

@[expose] def SU6Adaptation (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 1 .PSU 6 (𝒞 K) z →
      ∀ (hf : 1 ≤ f) (c : UCtx p f 5 (𝒞 K) K z) (nd : UNodes c) {β : Subgroup G},
        IsPartnerU c nd β → ¬ Commutes β (nd.j 3) → NonClassical.TE6Adaptation hf nd

theorem pieceSU6_of_adaptation (hMFZ : Gaps.FundNoncentral p) (hP1x : SU6P1x p f)
    (hexc : SU6NoG2D4 p f) (hAdapt : SU6Adaptation p f) : PieceSU6 p f := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, rfl⟩ := hshape
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .twistedE6 0 p f := ⟨Fact.out, hf, rfl⟩
  rcases NonClassical.routeD_typeU_five_of_adaptation S.odd hadm S.five S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1 hMFZ S.ih
    (fun c nd {_} hβ hn => hP1x G hnab K z S hS c nd hβ hn)
    (fun c nd {_} hβ hn => hexc G hnab K z S hS c nd hβ hn)
    (fun c nd {_} hβ hn => hAdapt G hnab K z S hS hf c nd hβ hn) with ⟨D, -, -⟩ | ⟨D, -, -⟩
  · exact ⟨D⟩
  · exact ⟨D⟩

structure Q3Inputs₅ : Prop where
  quasisimple : Q3.QuasisimpleConnected3
  core : Q3.CoreStep3
  fundamental : Q3.ClassicalIsFundamental3

theorem Q3Inputs₅.partOneSolvable (h : Q3Inputs₅) : PartOneSolvable :=
  Q3.partOneSolvable_of_remaining h.quasisimple h.core h.fundamental

structure CoreOpenWired₅ (p f : ℕ) [Fact p.Prime] : Prop where
  disconnected : Disconnected.DisconnectedInputs p f
  a2Datum : ConnectedA2.A2Datum p f
  a2P1 : ConnectedA2.A2P1 p f
  a2NoG2D4 : ConnectedA2.A2NoG2D4 p f
  a2Dichotomy : ModelFacts.StandardPairDichotomyFE p
  a2Injective : ConnectedA2.A2InjectiveCentral p f
  a2Orth : ConnectedA2.A2OrthEndpoint p f
  typeCSetup : SmallTypeCSetup p f
  psp6 : C3ShortNodeA2 p f
  frameCoverage : Balance.Bootstrap.FrameCoverage p f
  hybridRest : LayerGenerationHybridRest p
  exoticLevi : ExoticLeviBlockG2D4 p f
  frameNoF3 : Balance.Bootstrap.FrameNoF3 p f
  goodBootData : Balance.BootRank3.GoodBootDataExists p f
  bootNoTriple27 : p ^ f = 27 → BootNoTriple p f
  chainSLsTwo : ChainPieceSLsTwo p f
  su6P1x : SU6P1x p f
  su6NoG2D4 : SU6NoG2D4 p f
  su6Adaptation : SU6Adaptation p f
  chainSUsTwo : ChainPieceSUsTwo p f
  sp3 : PieceSp3 p f
  e7TorusFixed : E7TorusFixed p f
  e7SignPerp : E7SignPerp p f
  e8TorusFixed : E8TorusFixed p f
  e8Attachments : E8AttachmentsExcluded p f
  twinDTorus : TwinDTorusFixed₅ p f
  twinDSmall : TwinDSmall₄₆ p f
  twinSL4 : TwinSL4Bridge p f
  twinBTorus : TwinBTorusFixed p f
  twinBSmall : TwinBSmallPattern p f
  twinSp2Chain : TwinSp2Chain p f
  twinTDPattern : TwinTDPartnerPattern p f
  twinSU4Chain : TwinSU4Chain p f
  modelConn : RouteD.ModelConnFactNe p
  modelStar : RouteD.ModelStarFact p
  noG2D4 : RouteD.NoG2D4 p f
  orth : RowPiece p f Exotic.ShapeSingleOrth
  singleExc : RowPiece p f Exotic.ShapeSingleExc
  g2d4 : RowPiece p f Exotic.ShapeExoticG2D4
  d4 : RowPiece p f Exotic.ShapeExoticD4

theorem CoreOpenWired₅.pieceExotic (h : CoreOpenWired₅ p f) : PieceExotic p f :=
  (Exotic.ExoticPieces.mk (Exotic.mfTwinClassical p f) Exotic.mfTwinExc
    (rowSp6_of_recognition (psp6Recognition_of_shortNodes h.psp6) smallUpgrade_final)
    h.orth h.singleExc h.g2d4 h.d4).pieceExotic

theorem CoreOpenWired₅.toCoreStep (hGH : GH74SectionalModels)
    (hkg8 : Balance.LayerGenerationModel) (h : CoreOpenWired₅ p f) : CoreStep p f := by
  intro hp2 hq G _ _ _ hnab K z hz hBelow
  have hMFZ := Gaps.fundNoncentral p
  have hsect : CITSectionalFour := citSectionalFour_of_gh74_models hGH
  have hbootTriple : BootTriple p f :=
    Balance.Bootstrap.bootTriple_of_hybrid_final' h.hybridRest.toHybrid (fun _ _ => h.frameCoverage)
      (exoticLeviBlock_of_g2d4 h.exoticLevi) h.frameNoF3
  have hbootNoTriple : BootNoTriple p f :=
    bootNoTriple_of_parts hkg8 h.goodBootData h.bootNoTriple27
  have hmulti : MultiPiece p f := multiPiece_of_modelFactsNe h.modelConn h.modelStar h.noG2D4
  have hconn : SmallConnectedA2 p f :=
    ConnectedA2.smallConnectedA2_of_model_facts h.a2Datum h.a2P1 h.a2NoG2D4 h.a2Dichotomy
      h.a2Injective h.a2Orth
  have hshape := shapePiece_of_rows pieceSL7 (pieceSL6_of_five_final hMFZ)
    (rowSLs_of_parts (pieceSL3Big_of_chainTwo h.chainSLsTwo) hsect smallUpgrade_final
      (chainPieceSL45_of_setup hMFZ))
    pieceSU7 (pieceSU6_of_adaptation hMFZ h.su6P1x h.su6NoG2D4 h.su6Adaptation)
    (pieceSUs_of_parts' hMFZ (pieceSU3Big_of_chainTwo h.chainSUsTwo) hsect smallUpgrade_final)
    pieceSp4 h.sp3
    (pieceE7_of_exists (e7PartnerExists_of_torusFixed hMFZ h.e7TorusFixed))
    (pieceE8_of_exists
      (e8PartnerExists_of_inputs hMFZ h.e7SignPerp h.e8TorusFixed h.e8Attachments))
    (rowTwinD_of_pattern hMFZ (twinDPartnerPattern_of_parts₅ hMFZ h.twinDTorus h.twinDSmall))
    (pieceTwinSL4_of_bridge h.twinSL4)
    (rowTwinB_of_pattern hMFZ (twinBPartnerPattern_of_parts hMFZ h.twinBTorus h.twinBSmall))
    (pieceTwinSp2_of_chain h.twinSp2Chain) (rowTwinTD_of_pattern hMFZ h.twinTDPattern)
    (pieceTwinSU4_of_chain (WeakCT.SU4.su4SpinMinus_galois hp2 hq)
      (spinMinus6Generated_galois hp2) h.twinSU4Chain)
    (shapeExcluded_of_pieces pieceAllA1 (pieceNoA1_of_mfz hMFZ) h.pieceExotic)
  by_cases h2 : CFSG.Open.twoRank G ≤ 2
  · exact smallUpgrade_final G hnab hp2 hq K z hz
      (citRankTwo G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) h2)
  · have h3 : 3 ≤ CFSG.Open.twoRank G := by omega
    by_cases hgen : RouteD.DeltaConnected (𝒞 K) ∧ BootData p f (𝒞 K)
    · exact coreStep_generic hbootTriple hbootNoTriple hshape hmulti hnab hp2 hq hz
        hBelow hgen.1 hgen.2
    · exact coreStep_small hsect (Disconnected.smallDisconnected_of_inputs h.disconnected) hconn
        (smallTypeC_of_setup h.typeCSetup hshape hmulti) smallUpgrade_final hnab hp2 hq hz
        hBelow h3 hgen

theorem citSimplePerfect_of_wired₅ (hGH : GH74SectionalModels)
    (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₅ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep) :
    CITSimplePerfect :=
  Generic.citSimplePerfect_of_cases
    (Generic.citSimplePerfectSL2_of_citInductiveU
      (fun p f _ hp2 hq => ModelFacts.citInductiveU_of_coreStep_exc2
        ((hcore p f hp2 hq).toCoreStep hGH hkg8) ModelFacts.classicalMembersFundamentalExc2 hp2 hq)
      ModelFacts.modelClauseZero)
    (cit2A7Case_of_inputs GS TW (Hat2A7.localOddCentralStep2A7_of_B BS) Hat2A7.stepReduction2A7)

structure WiredInputs₅ : Prop where
  gh74 : GH74SectionalModels
  kg8 : Balance.LayerGenerationModel
  core : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₅ p f
  goldschmidt : Hat2A7.GoldschmidtMilestone
  twin : Hat2A7.TwinExclusion
  a7B : Hat2A7.A7BStep
  q3 : Q3Inputs₅
  tightLift : Q3.TightLift3
  normalOddSmall : NormalOddByQuaternionSmall

theorem WiredInputs₅.normalOdd (h : WiredInputs₅) : NormalOddByQuaternion :=
  normalOddByQuaternion_of_large_small
    (Q3.normalOddByQuaternionLarge_of_remaining h.q3.quasisimple h.q3.core h.q3.fundamental
      h.tightLift)
    h.normalOddSmall

theorem models_of_wired_inputs₅
    (hGH : GH74SectionalModels) (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₅ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep)
    (hP1 : PartOneSolvable) (hB : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_citSimplePerfect (citSimplePerfect_of_wired₅ hGH hkg8 hcore GS TW BS) hP1 hB G hFnonab
    z hz J hzJ hJ S hS

theorem WiredInputs₅.models (h : WiredInputs₅)
    (G : Type) [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)]
    (hFnonab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11) ∧
    (classicalInvolutionTightlyEmbedded J → CFSG.Blueprint.OddLieType (genFittingFStar G) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M11 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (genFittingFStar G) .M12) :=
  models_of_wired_inputs₅ h.gh74 h.kg8 h.core h.goldschmidt h.twin h.a7B h.q3.partOneSolvable
    h.normalOdd G hFnonab z hz J hzJ hJ S hS

theorem order_of_wired_inputs₅
    (hGH : GH74SectionalModels) (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₅ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep)
    (hP1 : PartOneSolvable) (hB : NormalOddByQuaternion)
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  orderForm_of_modelsForm (fun _ _ h => card_mem_lieOrdersChar_of_oddLieType h)
    (fun G _ _ _ hFnonab z hz J hzJ hJ S hS =>
      models_of_wired_inputs₅ hGH hkg8 hcore GS TW BS hP1 hB G hFnonab z hz J hzJ hJ S hS)
    G F hFnonab hFstar z hz J hzJ hJ S hS

theorem WiredInputs₅.order (h : WiredInputs₅)
    (G : Type) [Group G] [Finite G]
    (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a)
    (hFstar : Subgroup.centralizer (F : Set G) = ⊥)
    (z : G) (hz : orderOf z = 2)
    (J : Subgroup G) (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (classicalInvolutionWitness J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11)) ∧
    (classicalInvolutionTightlyEmbedded J →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card F ∈ lieOrdersChar p) ∨ Nonempty (F ≃* M11) ∨
        Nonempty (F ≃* classicalInvolutionM12)) :=
  order_of_wired_inputs₅ h.gh74 h.kg8 h.core h.goldschmidt h.twin h.a7B h.q3.partOneSolvable
    h.normalOdd G F hFnonab hFstar z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution.MilestoneAssembly
