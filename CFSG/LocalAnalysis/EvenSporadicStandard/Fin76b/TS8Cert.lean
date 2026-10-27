module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Rest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Root
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentFinal

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

theorem fin76bOuterUCent_of_cert :
    Fin76bOuterUCent := by
  intro G _ _ L z t T E _ hJ hE hW S hS2 hSC hSmax hzS hD8
  have hEt : t ∈ E := hE.econfig.t_mem
  have htc : ∀ e ∈ E, e * t = t * e := fun e he => hE.cfg.t_central e (hE.E_le_T he)
  have htS : t ∈ S := mem_of_maximal hS2 hSC hSmax hE.cfg.t_sq hEt htc
  have hSE : ∀ s ∈ S, ∀ e ∈ E, s * e = e * s := fun s hs e he =>
    (mem_centralizer_iff.1 (hSC hs) e he).symm
  have hRC : RootFactsClass ↥L :=
    rootFactsClass_of_sporadic J2.rootFactsClass_P J3.rootFactsClass_j3P hJ
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    let φ : ↥ComponentClassification.J2Cover.Models.P ≃* ↥L :=
      ((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm
    have hU : ULabelClass ↥L J2.uMulJ2 J2.uIdxJ2 := ULabelClass.of_mulEquiv φ J2.uLabelClass_P
    obtain ⟨eltE, hlab⟩ := hE.exists_eLabelling hW hRC hU
    exact exists_X_of_spec hD8.some hlab htS hSE J2.uSpec_j2
  · obtain ⟨e⟩ := hL
    let φ : ↥j3P ≃* ↥L := j3PermEquiv.symm.trans e.symm
    have hU : ULabelClass ↥L J3.uMulJ3 J3.uIdxJ3 := ULabelClass.of_mulEquiv φ J3.uLabelClass_j3P
    obtain ⟨eltE, hlab⟩ := hE.exists_eLabelling hW hRC hU
    exact exists_X_of_spec hD8.some hlab htS hSE J3.uSpec_j3


theorem fin76bOuterS8_of_s8₃_cert
    (h3 : Fin76bOuterS8₃) : Fin76bOuterS8 :=
  fin76bOuterS8_of_s8₃ fin76bOuterUCent_of_cert h3

theorem fin76bOuterS8_of_s8₄_cert
    (h4 : Fin76bOuterS8₄) : Fin76bOuterS8 :=
  fin76bOuterS8_of_s8₃_cert (fin76bOuterS8₃_of_s8₄ h4)

end CFSG.EvenSporadicStandard.Fin76b
