module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanBalEnd
public import CFSG.LocalAnalysis.OddStandard.ONanEndConsumer
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.OddStandard.L34EvenSylow
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3085Base
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.GrSLit.ONanBal

open Subgroup CFSG.OddStandard CFSG.OddStandard.ONanRec CFSG.OddStandard.ONanRec.F2

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G}

theorem balanced_of_fusCtx
    [IsSimpleGroup G] (D : FusCtx G v1 v2 v3 s t) (hF : ThmC.ThmCFull) (hone : OneClass G) :
    Balanced G := by
  intro j hj
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone (invRep v1 v2 v3 s t 0) j (D.orderOf_rep 0) hj)
  have hθ : theta j = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    have h1 := conj_mem_theta c⁻¹ hk
    rw [show c⁻¹ * j * c⁻¹⁻¹ = invRep v1 v2 v3 s t 0 by rw [← hc]; group,
      theta_z_eq_bot D hF hone, mem_bot] at h1
    rw [mem_bot]
    calc k = c * (c⁻¹ * k * c⁻¹⁻¹) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  rw [oddCore_eq_pPrimeCore_two']
  exact (map_eq_bot_iff_of_injective _ (centralizer ({j} : Set G)).subtype_injective).1 hθ

theorem stageU_ON_of_thmC
    (hF : ThmC.ThmCFull) (hgold : CFSG.Goldschmidt.CoreStatement) :
    StageU CFSG.Blueprint.NativeSporadic.ON := by
  intro G _ _ _ hna _ S T e
  obtain ⟨v1, v2, v3, s, t, hfr, hP, hz⟩ := stageA5_ON_cert G S T e
  let D := FusCtx.ofStage hna hfr hz S hP.symm
  exact balanced_of_fusCtx D hF (D.oneClass hna hgold)

end CFSG.ComponentClassification.GrSLit.ONanBal
