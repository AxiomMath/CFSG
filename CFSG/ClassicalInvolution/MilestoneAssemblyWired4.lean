module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired3
public import CFSG.ClassicalInvolution.Balance.BootNoTriple
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTripleFinal
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAll
public import CFSG.ClassicalInvolution.Q3.Main
public import CFSG.ClassicalInvolution.Q3.SP3
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc
public import CFSG.ClassicalInvolution.RouteD.GapsToralD
public import CFSG.ClassicalInvolution.RouteD.SmallTwinSLs
public import CFSG.ClassicalInvolution.RouteD.SmallTwinSUs
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge
public import CFSG.ClassicalInvolution.RouteD.TypeUThreePiece
public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthRows
public import CFSG.ClassicalInvolution.SmallCases.UpgradeFinal
public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusFinal
public import CFSG.Sporadic.Mathieu.M11
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
public import CFSG.ClassicalInvolution.Models.TwistedPairs

public section

namespace CFSG.ClassicalInvolution.MilestoneAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.Open (genFittingFStar IsSubnormal classicalInvolutionWitness
  classicalInvolutionTightlyEmbedded lieOrdersChar M11 classicalInvolutionM12)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => Generic.CoreAssembly.conjClass

theorem smallUpgrade_final : SmallUpgrade p f :=
  Upgrade.smallUpgrade_of_fundamentalExc2 ModelFacts.classicalMembersFundamentalExc2

theorem pieceSUs_of_parts' (hMFZ : Gaps.FundNoncentral p) (hbig : PieceSU3Big p f)
    (hs4 : CITSectionalFour) (hup : SmallUpgrade p f) : PieceSUs p f := by
  intro a t n hshape
  obtain ⟨rfl, rfl, h3, h5⟩ := hshape
  by_cases hn3 : n = 3
  · subst hn3
    exact shapePiece_su3 hbig citRankTwo hs4 hup
  by_cases hn4 : n = 4
  · subst hn4
    exact shapePiece_su4 hMFZ
  have hn : n = 5 := by omega
  subst hn
  intro G _ _ _ hnab K z S hS
  obtain ⟨D, -, -⟩ := routeD_typeU_four hMFZ S.odd S.five S.inClass S.exact
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS.exists_two_components S.p1
  exact ⟨D⟩

@[expose] def TwinTDPartnerPattern (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 4 ≤ m →
      LocalShapeT p f 2 .POmegaMinus m (𝒞 K) z → ∀ β ∈ 𝒞 K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (𝒞 K) K β z → PartnerPatternMinus p f m (𝒞 K) K β t

theorem rowTwinTD_of_pattern (hMFZ : Gaps.FundNoncentral p) (h : TwinTDPartnerPattern p f) :
    RowPiece p f ShapeTwinTD := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaMinus (n + 2 - 2) (𝒞 K) z := by rw [hn']; exact hS
  have hf : f ≠ 0 := by
    rintro rfl
    simpa using S.five
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField S.odd S.five
  obtain ⟨D, -, -⟩ := routeD_typeTwistedD_of_pattern S.odd S.five (spinMinus6Generated_galois S.odd)
    hMFZ hS3 (n := n + 2) (by omega) S.inClass S.exact (mem_conjClass_self K) (single_class K)
    S.conn S.cls hS' S.p1 (by
      intro β hβ t ht hKβ hfix
      have := h G hnab K z S n hn hS β hβ t ht hKβ hfix
      rwa [hn'])
  exact ⟨D⟩

@[expose] def TwinDTorusFixed (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (m : ℕ) (_ : 7 ≤ m),
      LocalShapeT p f 2 .POmegaPlus m (𝒞 K) z →
      ∃ c : TCtx p f .POmegaPlus m (𝒞 K) K z, ∀ β ∈ 𝒞 K, ∀ t : G,
        ∀ ht : IsClassicalMember p f β t,
          ∀ hKβ : (∃ W, LinearBlockStandardPair (GaloisField p f) W K β),
            HasFixedMember (𝒞 K) K β z →
            Gaps.TorusFixedD (by omega : 3 ≤ m) c
              (partner_involution_commutes c.hp2 c.hz ht hKβ)

@[expose] def TwinDSmallPattern (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, 4 ≤ m → m ≤ 6 →
      LocalShapeT p f 2 .POmegaPlus m (𝒞 K) z → ∀ β ∈ 𝒞 K, ∀ t : G,
        IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (𝒞 K) K β z → PartnerPatternD p f m (𝒞 K) K β t

theorem twinDPartnerPattern_of_parts (hMFZ : Gaps.FundNoncentral p) (hT : TwinDTorusFixed p f)
    (hS : TwinDSmallPattern p f) : TwinDPartnerPattern p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases h7 : 7 ≤ m
  · obtain ⟨c, hc⟩ := hT G hnab K z S m h7 hshape
    exact Gaps.PartnerPatternD.of_torusFixed h7 hMFZ c (single_class K) hshape hβ ht hKβ hfix
      (hc β hβ t ht hKβ hfix)
  · exact hS G hnab K z S m hm (by omega) hshape β hβ t ht hKβ hfix

theorem bootNoTriple_of_parts (hkg8 : Balance.LayerGenerationModel)
    (hgood : Balance.BootRank3.GoodBootDataExists p f) (h27 : p ^ f = 27 → BootNoTriple p f) :
    BootNoTriple p f := by
  by_cases h : p ^ f = 27
  · exact h27 h
  · exact Balance.BootRank3.bootNoTriple_of_goodBootData h hkg8 hgood

theorem m11Facts : Q3.M11Facts :=
  ⟨CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2, CFSG.Sporadic.Mathieu.card_M11⟩

structure Q3Inputs : Prop where
  quasisimple : Q3.QuasisimpleConnected3
  core : Q3.CoreStep3
  fundamental : Q3.ClassicalIsFundamental3
  centralLift : CentralLift 3
  m11Branch : Q3.M11Branch3

theorem Q3Inputs.partOneSolvable (h : Q3Inputs) : PartOneSolvable :=
  Q3.partOneSolvable_of_parts Q3.SP3.solvableConnected3 h.quasisimple h.core h.fundamental
    h.centralLift h.m11Branch m11Facts

@[expose] def NormalOddByQuaternionSmall : Prop :=
  NormalOddByQuaternionUnder fun {G} _ _ _ => TwoSubgroupsFourGenerated (genFittingFStar G)

theorem normalOddByQuaternion_of_large_small (hL : Q3.NormalOddByQuaternionLarge)
    (hS : NormalOddByQuaternionSmall) : NormalOddByQuaternion := by
  intro G _ _ _ hnab R S hS' t ht hto hRC hRn h2 _
  by_cases h : TwoSubgroupsFourGenerated (genFittingFStar G)
  · exact hS G hnab R S hS' t ht hto hRC hRn h2 h
  · exact hL G hnab R S hS' t ht hto hRC hRn h2 h

structure CoreOpenWired₄ (p f : ℕ) [Fact p.Prime] : Prop where
  disconnected : SmallDisconnected p f
  connectedA2 : ConnectedA2.ConnectedA2Inputs p f
  typeCSetup : SmallTypeCSetup p f
  psp6 : PSp6Recognition p f
  frameCoverage : Balance.Bootstrap.FrameCoverage p f
  exoticLevi : Balance.Bootstrap.ExoticLeviBlock p f
  frameNoF3 : Balance.Bootstrap.FrameNoF3 p f
  goodBootData : Balance.BootRank3.GoodBootDataExists p f
  bootNoTriple27 : p ^ f = 27 → BootNoTriple p f
  chainSLsTwo : ChainPieceSLsTwo p f
  phanE6 : PhanE6 p f
  chainSUsTwo : ChainPieceSUsTwo p f
  sp3 : PieceSp3 p f
  e7 : E7PartnerExists p f
  e8 : E8PartnerExists p f
  twinDTorus : TwinDTorusFixed p f
  twinDSmall : TwinDSmallPattern p f
  twinSL4 : PieceTwinSL4 p f
  twinB : TwinBPartnerPattern p f
  partnerSp2 : PartnerPieceTwinSp2 p f
  twinTDPattern : TwinTDPartnerPattern p f
  partnerSU4 : PartnerPieceTwinSU4 p f
  multi : MultiPiece p f
  excLayer : Exotic.ExcLayer p f
  orth : RowPiece p f Exotic.ShapeSingleOrth
  singleExc : RowPiece p f Exotic.ShapeSingleExc
  g2d4 : RowPiece p f Exotic.ShapeExoticG2D4
  d4 : RowPiece p f Exotic.ShapeExoticD4

theorem CoreOpenWired₄.pieceExotic (h : CoreOpenWired₄ p f) : PieceExotic p f :=
  (Exotic.ExoticPieces.mk (Exotic.mfTwinClassical p f) (Exotic.mfTwinExc_of_layer h.excLayer)
    (rowSp6_of_recognition h.psp6 smallUpgrade_final) h.orth h.singleExc h.g2d4 h.d4).pieceExotic

theorem CoreOpenWired₄.toCoreStep (hGH : GH74SectionalModels)
    (hkg8 : Balance.LayerGenerationModel) (h : CoreOpenWired₄ p f) : CoreStep p f := by
  intro hp2 hq G _ _ _ hnab K z hz hBelow
  have hMFZ := Gaps.fundNoncentral p
  have hsect : CITSectionalFour := citSectionalFour_of_gh74_models hGH
  have hbootTriple : BootTriple p f :=
    Balance.Bootstrap.bootTriple_of_model_final' hkg8 (fun _ _ => h.frameCoverage) h.exoticLevi
      h.frameNoF3
  have hbootNoTriple : BootNoTriple p f :=
    bootNoTriple_of_parts hkg8 h.goodBootData h.bootNoTriple27
  have hshape := shapePiece_of_rows pieceSL7 (pieceSL6_of_five_final hMFZ)
    (rowSLs_of_parts (pieceSL3Big_of_chainTwo h.chainSLsTwo) hsect smallUpgrade_final
      (chainPieceSL45_of_setup hMFZ))
    pieceSU7 (pieceSU6_of_phanE6 hMFZ h.phanE6)
    (pieceSUs_of_parts' hMFZ (pieceSU3Big_of_chainTwo h.chainSUsTwo) hsect smallUpgrade_final)
    pieceSp4 h.sp3 (pieceE7_of_exists h.e7) (pieceE8_of_exists h.e8)
    (rowTwinD_of_pattern hMFZ (twinDPartnerPattern_of_parts hMFZ h.twinDTorus h.twinDSmall))
    h.twinSL4 (rowTwinB_of_pattern hMFZ h.twinB) (pieceTwinSp2_of_partner h.partnerSp2)
    (rowTwinTD_of_pattern hMFZ h.twinTDPattern)
    (pieceTwinSU4_of_partner (WeakCT.SU4.su4SpinMinus_galois hp2 hq)
      (spinMinus6Generated_galois hp2) h.partnerSU4)
    (shapeExcluded_of_pieces pieceAllA1 (pieceNoA1_of_mfz hMFZ) h.pieceExotic)
  by_cases h2 : CFSG.Open.twoRank G ≤ 2
  · exact smallUpgrade_final G hnab hp2 hq K z hz
      (citRankTwo G hnab z hz.orderOf_eq_two K hz.mem hz.subnormal
        (witness_of_isClassicalMember hp2 hq hz) (not_isSolvable_of_isClassicalMember hz) h2)
  · have h3 : 3 ≤ CFSG.Open.twoRank G := by omega
    by_cases hgen : RouteD.DeltaConnected (𝒞 K) ∧ BootData p f (𝒞 K)
    · exact coreStep_generic hbootTriple hbootNoTriple hshape h.multi hnab hp2 hq hz
        hBelow hgen.1 hgen.2
    · exact coreStep_small hsect h.disconnected
        (ConnectedA2.smallConnectedA2_of_inputs h.connectedA2)
        (smallTypeC_of_setup h.typeCSetup hshape h.multi) smallUpgrade_final hnab hp2 hq hz
        hBelow h3 hgen

theorem citSimplePerfect_of_wired₄ (hGH : GH74SectionalModels)
    (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₄ p f)
    (GS : Hat2A7.GoldschmidtMilestone) (TW : Hat2A7.TwinExclusion) (BS : Hat2A7.A7BStep) :
    CITSimplePerfect :=
  Generic.citSimplePerfect_of_cases
    (Generic.citSimplePerfectSL2_of_citInductiveU
      (fun p f _ hp2 hq => ModelFacts.citInductiveU_of_coreStep_exc2
        ((hcore p f hp2 hq).toCoreStep hGH hkg8) ModelFacts.classicalMembersFundamentalExc2 hp2 hq)
      ModelFacts.modelClauseZero)
    (cit2A7Case_of_inputs GS TW (Hat2A7.localOddCentralStep2A7_of_B BS) Hat2A7.stepReduction2A7)

structure WiredInputs₄ : Prop where
  gh74 : GH74SectionalModels
  kg8 : Balance.LayerGenerationModel
  core : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₄ p f
  goldschmidt : Hat2A7.GoldschmidtMilestone
  twin : Hat2A7.TwinExclusion
  a7B : Hat2A7.A7BStep
  q3 : Q3Inputs
  tightLift : Q3.TightLift3
  normalOddSmall : NormalOddByQuaternionSmall

theorem WiredInputs₄.normalOdd (h : WiredInputs₄) : NormalOddByQuaternion :=
  normalOddByQuaternion_of_large_small
    (Q3.normalOddByQuaternionLarge_of_parts Q3.SP3.solvableConnected3 h.q3.quasisimple h.q3.core
      h.q3.fundamental h.q3.centralLift h.q3.m11Branch m11Facts h.tightLift)
    h.normalOddSmall

theorem models_of_wired_inputs₄
    (hGH : GH74SectionalModels) (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₄ p f)
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
  models_of_citSimplePerfect (citSimplePerfect_of_wired₄ hGH hkg8 hcore GS TW BS) hP1 hB G hFnonab
    z hz J hzJ hJ S hS

theorem WiredInputs₄.models (h : WiredInputs₄)
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
  models_of_wired_inputs₄ h.gh74 h.kg8 h.core h.goldschmidt h.twin h.a7B h.q3.partOneSolvable
    h.normalOdd G hFnonab z hz J hzJ hJ S hS

theorem order_of_wired_inputs₄
    (hGH : GH74SectionalModels) (hkg8 : Balance.LayerGenerationModel)
    (hcore : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 2 → 5 ≤ p ^ f → CoreOpenWired₄ p f)
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
      models_of_wired_inputs₄ hGH hkg8 hcore GS TW BS hP1 hB G hFnonab z hz J hzJ hJ S hS)
    G F hFnonab hFstar z hz J hzJ hJ S hS

theorem WiredInputs₄.order (h : WiredInputs₄)
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
  order_of_wired_inputs₄ h.gh74 h.kg8 h.core h.goldschmidt h.twin h.a7B h.q3.partOneSolvable
    h.normalOdd G F hFnonab hFstar z hz J hzJ hJ S hS

end CFSG.ClassicalInvolution.MilestoneAssembly
