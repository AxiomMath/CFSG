module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakCorr
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitPointed

import CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327Proof
import CFSG.Assembly.Defs
import CFSG.GroupTheory.PCore.Defs
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.Assembly.Reduction
import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutWClass
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Comm
import CFSG.LocalAnalysis.ComponentClassification.CTUFooteConjugate
import CFSG.LocalAnalysis.ComponentClassification.Foote5SolRepoint
import CFSG.LocalAnalysis.ComponentClassification.Foote5SolStar
import CFSG.LocalAnalysis.ComponentClassification.Foote5SolForward
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeDB
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStepFour
import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieL1
import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalGrowth
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Chain
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.Blueprint.OddStandardExact
import CFSG.Blueprint.RecognitionDefs
import CFSG.Certificates.LiftedSchreierData
import CFSG.LocalAnalysis.ComponentClassification.Foote5WMFree
import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUSetup
import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassPoint
import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.Sporadic.Bridge.BOrder
import CFSG.Sporadic.Bridge.BSurjInputs
import CFSG.Sporadic.Fi24.Faithful
import CFSG.Sporadic.Fi24.SepSpec
import CFSG.Sporadic.Fi24.Simple
import CFSG.Sporadic.Schreier.RuLOdd
import CFSG.Sporadic.Schreier.RuZClass
import CFSG.Sporadic.ThSchreier.GlobalIndexBase
import Certificates.Certificate1000
import Certificates.Certificate1001
import Certificates.Certificate1001Base
import Certificates.Certificate10027
import Certificates.Certificate1004
import Certificates.Certificate1005
import Certificates.Certificate1006
import Certificates.Certificate1007
import Certificates.Certificate1007Base
import Certificates.Certificate1008
import Certificates.Certificate10090
import Certificates.Certificate10090Base
import Certificates.Certificate10095
import Certificates.Certificate10095Base
import Certificates.Certificate1010
import Certificates.Certificate10100
import Certificates.Certificate10101
import Certificates.Certificate10102
import Certificates.Certificate10104
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate1011
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate10115
import Certificates.Certificate10115Base
import Certificates.Certificate10116
import Certificates.Certificate10116Base
import Certificates.Certificate10117
import Certificates.Certificate10117Base
import Certificates.Certificate10118
import Certificates.Certificate10118Base
import Certificates.Certificate10119
import Certificates.Certificate10119Base
import Certificates.Certificate10123
import Certificates.Certificate10123Base
import Certificates.Certificate1013
import Certificates.Certificate1014
import Certificates.Certificate1014Base
import Certificates.Certificate1015
import Certificates.Certificate1017
import Certificates.Certificate1018
import Certificates.Certificate1018Base
import Certificates.Certificate1019
import Certificates.Certificate1021
import Certificates.Certificate14953
import Certificates.Certificate16018
import Certificates.Certificate16041
import Certificates.Certificate2051
import Certificates.Certificate2053
import Certificates.Certificate2056
import Certificates.Certificate2057
import Certificates.Certificate2058
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2108
import Certificates.Certificate2109
import Certificates.Certificate2130
import Certificates.Certificate2135
import Certificates.Certificate2136
import Certificates.Certificate2139
import Certificates.Certificate2140
import Certificates.Certificate2145
import Certificates.Certificate2160
import Certificates.Certificate2166
import Certificates.Certificate2207
import Certificates.Certificate2211
import Certificates.Certificate2213
import Certificates.Certificate2215
import Certificates.Certificate2216
import Certificates.Certificate2216Base
import Certificates.Certificate2217
import Certificates.Certificate2238
import Certificates.Certificate2239
import Certificates.Certificate2242
import Certificates.Certificate2243
import Certificates.Certificate2244
import Certificates.Certificate2245
import Certificates.Certificate2246
import Certificates.Certificate2251
import Certificates.Certificate2254
import Certificates.Certificate2254Base
import Certificates.Certificate2255
import Certificates.Certificate2261
import Certificates.Certificate2269
import Certificates.Certificate2274
import Certificates.Certificate2293
import Certificates.Certificate2294
import Certificates.Certificate2304
import Certificates.Certificate2305
import Certificates.Certificate2308
import Certificates.Certificate2309
import Certificates.Certificate2311
import Certificates.Certificate2313
import Certificates.Certificate2314
import Certificates.Certificate2315
import Certificates.Certificate2317
import Certificates.Certificate2323
import Certificates.Certificate2324
import Certificates.Certificate2325
import Certificates.Certificate3037
import Certificates.Certificate3037Base
import Certificates.Certificate3038
import Certificates.Certificate3038Base
import Certificates.Certificate3084
import Certificates.Certificate3114
import Certificates.Certificate3148
import Certificates.Certificate3148Base
import Certificates.Certificate3150
import Certificates.Certificate3150Base
import Certificates.Certificate3151
import Certificates.Certificate3151Base
import Certificates.Certificate3152
import Certificates.Certificate3152Base
import Certificates.Certificate3153
import Certificates.Certificate3153Base
import Certificates.Certificate3154
import Certificates.Certificate3154Base
import Certificates.Certificate3171
import Certificates.Certificate3171Base
import Certificates.Certificate3173
import Certificates.Certificate3173Base
import Certificates.Certificate5133
import Certificates.Certificate6006
import Certificates.Certificate8064
import Certificates.Certificate9201

public section

universe u

namespace CFSG.ComponentClassification.Walter86

open CFSG Subgroup
open CFSG.ComponentClassification.FooteLit
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.UnbalancedGS
open CFSG.GH74.GLS
open scoped commutatorElement

section SectionKernel

variable {G : Type u} [Group G]

theorem centralizerSection_pPrimeCoreOf_eq_coreActionKernel (L : Subgroup G) :
    CFSG.GH74.GLS.centralizerSection L (CFSG.GH74.GLS.pPrimeCoreOf 2 L) =
      CFSG.ComponentClassification.UnbalancedLayer.coreActionKernel L := by
  ext c
  constructor
  · rintro ⟨hcN, hcO, hcComm⟩
    refine CFSG.ComponentClassification.UnbalancedLayer.mem_coreActionKernel.mpr
      ⟨hcN, fun k hk => ?_⟩
    have hcinv : c⁻¹ ∈ CFSG.GH74.GLS.centralizerSection L
        (CFSG.GH74.GLS.pPrimeCoreOf 2 L) :=
      (CFSG.GH74.GLS.centralizerSection L
        (CFSG.GH74.GLS.pPrimeCoreOf 2 L)).inv_mem ⟨hcN, hcO, hcComm⟩
    obtain ⟨-, -, hcinvComm⟩ := hcinv
    have h := hcinvComm k⁻¹ (L.inv_mem hk)
    simpa [commutatorElement_def, CFSG.GH74.GLS.pPrimeCoreOf] using h
  · intro hc
    obtain ⟨hcN, hcComm⟩ :=
      CFSG.ComponentClassification.UnbalancedLayer.mem_coreActionKernel.mp hc
    refine ⟨hcN, ?_, fun k hk => ?_⟩
    · exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := L) (K := pPrimeCore 2 ↥L) hcN
    · have hcinv : c⁻¹ ∈ CFSG.ComponentClassification.UnbalancedLayer.coreActionKernel L :=
        (CFSG.ComponentClassification.UnbalancedLayer.coreActionKernel L).inv_mem
          (CFSG.ComponentClassification.UnbalancedLayer.mem_coreActionKernel.mpr ⟨hcN, hcComm⟩)
      obtain ⟨-, hcinvComm⟩ :=
        CFSG.ComponentClassification.UnbalancedLayer.mem_coreActionKernel.mp hcinv
      have h := hcinvComm k⁻¹ (L.inv_mem hk)
      simpa [commutatorElement_def, CFSG.GH74.GLS.pPrimeCoreOf] using h

end SectionKernel

section SectionPumpUp

variable {G : Type u} [Group G]

theorem pumpUp_two_eq_conjClosure_gsFixedLayer (L : Subgroup G) (t : G) :
    CFSG.GH74.GLS.pumpUp 2 L t =
      CFSG.ComponentClassification.FooteLit.conjClosure
        (CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer L t)
        (CFSG.ComponentClassification.FooteLit.twoLayerIn
          (Subgroup.centralizer ({t} : Set G))) := by
  rw [CFSG.GH74.GLS.pumpUp,
    CFSG.ComponentClassification.FooteLit.conjClosure_eq_iSup,
    CFSG.ComponentClassification.FooteLit.twoLayerIn,
    CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer,
    CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.pLayerOf_eq_map' 2
      (Subgroup.centralizer ({t} : Set G)),
    CFSG.GH74.GLS.Stage1.Thm2.Recip.IG327B.pLayerOf_eq_map' 2
      (L ⊓ Subgroup.centralizer ({t} : Set G))]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    refine le_iSup₂_of_le g⁻¹ (Subgroup.inv_mem _ hg) ?_
    rw [CFSG.conjugate, inv_inv]
  · refine iSup₂_le fun e he => ?_
    exact le_iSup₂_of_le e⁻¹ (Subgroup.inv_mem _ he) le_rfl

end SectionPumpUp

section SectionFinite

variable {G : Type} [Group G] [Finite G]

theorem gsWeakCorr_of_pumpUpLT {x t : G} {L J : Subgroup G}
    (h : CFSG.GH74.GLS.PumpUpLT 2 x L t J) :
    CFSG.ComponentClassification.GrSLit.GSWeakCorr x L t J := by
  obtain ⟨hxILo, htILo, htx, htSec, hJpump⟩ := h
  obtain ⟨hx2, -, hxL⟩ := hxILo
  obtain ⟨ht2, -, htJ⟩ := htILo
  obtain ⟨hLx, hLpc⟩ := hxL
  obtain ⟨hJt, hJpc⟩ := htJ
  obtain ⟨hJle, -⟩ := hJpump
  have htx' : t * x = x * t := mem_centralizer_singleton_iff.mp htx
  have htK : t ∈ CFSG.ComponentClassification.UnbalancedLayer.coreActionKernel L := by
    rw [← centralizerSection_pPrimeCoreOf_eq_coreActionKernel L]
    exact htSec
  obtain ⟨htN, htComm⟩ :=
    CFSG.ComponentClassification.UnbalancedLayer.mem_coreActionKernel.mp htK
  have hLsub : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := hLpc
    exact hs
  have hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    CFSG.ComponentClassification.FooteLit.isQuasisimple_quotient_of_isPComponent hLx hLpc
  have hTpc : IsPComponent 2
      ((CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer L t).subgroupOf
        (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G))) :=
    CFSG.ComponentClassification.UnbalancedCorr.gsFixedLayer_isPComponent hLx hLsub htx ht2
      htN hLq htComm
  set H : Subgroup G := Subgroup.centralizer ({t} : Set G) with hH
  have hxH : x ∈ H := by
    rw [hH]
    exact mem_centralizer_singleton_iff.mpr htx'.symm
  have hTleHX : CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer L t ≤
      H ⊓ Subgroup.centralizer ({x} : Set G) := by
    rw [hH]
    exact le_inf
      ((CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer_le_inf L t).trans inf_le_right)
      ((CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer_le_inf L t).trans
        (inf_le_left.trans hLx))
  have hTpc' : IsPComponent 2
      ((CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer L t).subgroupOf
        (H ⊓ Subgroup.centralizer ({x} : Set G))) := by
    rw [hH, inf_comm]
    exact hTpc
  obtain ⟨B, hBH, hBpc, hTB, hcl, -⟩ :=
    CFSG.ComponentClassification.FooteLit.foote_lemma_2_1_iv_subgroup
      (H := H) (a := x) (K := CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer L t)
      hxH hx2 hTleHX hTpc'
  have hBxH : CFSG.conjugate B x ≤ H :=
    CFSG.ComponentClassification.UnbalancedCorr.conjugate_le_of_mem hBH hxH
  have hBxpc : IsPComponent 2 ((CFSG.conjugate B x).subgroupOf H) :=
    CFSG.ComponentClassification.UnbalancedCorr.isPComponent_conjugate_subgroupOf hxH hBpc
  have hJle' : J ≤ B ⊔ CFSG.conjugate B x := by
    have hBeq : CFSG.GH74.GLS.pumpUp 2 L t =
        CFSG.ComponentClassification.FooteLit.conjClosure
          (CFSG.ComponentClassification.UnbalancedGS.gsFixedLayer L t)
          (CFSG.ComponentClassification.FooteLit.twoLayerIn H) := by
      rw [pumpUp_two_eq_conjClosure_gsFixedLayer]
    have h := hJle
    rw [hBeq, hcl] at h
    exact h
  have hJB : J = B ∨ J = CFSG.conjugate B x :=
    CFSG.ComponentClassification.GSLit.eq_or_eq_of_le_sup hJt hJpc hBH hBpc hBxH hBxpc hJle'
  have hxx : x * x = 1 := by
    rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hsup : J ⊔ CFSG.conjugate J x = B ⊔ CFSG.conjugate B x :=
    CFSG.ComponentClassification.Foote5.SolMax.sup_conjugate_eq_of_mem_pair hxx hJB
  refine ⟨hx2, ht2, htx'.symm, hLx, hLpc, hJt, hJpc, htN, htComm, ?_⟩
  rw [hsup]
  exact hTB

end SectionFinite

end CFSG.ComponentClassification.Walter86
