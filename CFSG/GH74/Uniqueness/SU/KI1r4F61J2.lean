module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Mod
public import CFSG.GH74.Uniqueness.SU.KI1r4F61Sp
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.GH74.Uniqueness.SU.KI1r4F61J2Inputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4F61J2Inputs
public import Certificates.Certificate3139
public import Certificates.Certificate5136
public import Certificates.Certificate10019
public import CFSG.Foundations
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Uniqueness.SU.KI1r3FamBender
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.J2M

open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native

theorem check_A :
    pairCheck autStrong[0]! (wordArr cent2BStrong [1, 0])
    (wordArr cent2BStrong [1, 1, 1]) = true :=
  Certificates.certificate5136.1

theorem check_TwoA :
    pairCheck twoAArr (wordArr cent2AStrong [0, 0, 0, 0, 0])
    (wordArr cent2AStrong [1, 0, 1, 0, 1, 1]) = true :=
  Certificates.certificate5136.2.1

theorem check_U :
    pairCheck outerArr (wordArr centOuterStrong [0, 1, 1, 0, 0, 1, 1, 0])
    (wordArr centOuterStrong [1, 1, 1]) = true :=
  Certificates.certificate5136.2.2

theorem modE4_of_pairCheck
    {r : Equiv.Perm (Fin 315)} {rt U V : Array ℕ} (hr : Rep 315 rt r)
    (h : pairCheck rt U V = true) : ModE4 P r := by
  simp only [pairCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hUi, hVi⟩, hUP⟩, hVP⟩, hUc⟩, hVc⟩, hU2⟩, hV2⟩, hU1⟩, hV1⟩, hUV⟩, hUVc⟩ := h
  obtain ⟨rU, -⟩ := rep_permOfArr hUi
  obtain ⟨rV, -⟩ := rep_permOfArr hVi
  refine ⟨permOfArr 315 U, permOfArr 315 V, (mem_P_iff rU).1 hUP, (mem_P_iff rV).1 hVP, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    have := (eqA_iff rU rep_idA).2 h1
    rw [hU1] at this
    exact Bool.noConfusion this
  · intro h1
    have := (eqA_iff rV rep_idA).2 h1
    rw [hV1] at this
    exact Bool.noConfusion this
  · intro h1
    have := (eqA_iff rU rV).2 h1
    rw [hUV] at this
    exact Bool.noConfusion this
  · rw [sq]
    exact eq_of_eqA (rep_compA rU rU) rep_idA hU2
  · rw [sq]
    exact eq_of_eqA (rep_compA rV rV) rep_idA hV2
  · exact eq_of_eqA (rep_compA rU rV) (rep_compA rV rU) hUVc
  · exact (eq_of_eqA (rep_compA rU hr) (rep_compA hr rU) hUc).symm
  · exact (eq_of_eqA (rep_compA rV hr) (rep_compA hr rV) hVc).symm

theorem modE4_A :
    ModE4 P permA := modE4_of_pairCheck rep_permA check_A

theorem modE4_TwoA :
    ModE4 P permTwoA := modE4_of_pairCheck rep_permTwoA check_TwoA

theorem modE4_U :
    ModE4 P permU := modE4_of_pairCheck rep_permU check_U

end CFSG.GH74.Uniqueness.SU.K.R4.J2M

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG.ComponentClassification.J2Cover CFSG.GH74.KGroups

theorem strictFix_J2P :
    StrictFix ↥P := by
  let M : AutModel ↥P (Equiv.Perm (Fin 315)) :=
    AutModel.ofRealization P R (MulEquiv.refl ↥P) rAutEquiv fun σ x => rConj_apply σ x
  refine strictFix_of_model M fun g hg hg2 => ?_
  change g ∈ R at hg
  change ModE4 P g
  rcases mem_P_or_coset hg with hgP | hgU
  · by_cases hg1 : g = 1
    · rw [hg1]
      exact J2M.modE4_A.one
    · have ho : orderOf g = 2 := orderOf_eq_prime hg2 hg1
      obtain ⟨r, hr, c, hc, e⟩ := inner_classes.1 g hgP ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [e]
      rcases hr with rfl | rfl
      · exact J2M.modE4_A.conj hc
      · exact J2M.modE4_TwoA.conj hc
  · have hg1 : g ≠ 1 := by
      rintro rfl
      have hgU' : permU⁻¹ ∈ P := by simpa using hgU
      exact permU_not_mem (by simpa using P.inv_mem hgU')
    have ho : orderOf g = 2 := orderOf_eq_prime hg2 hg1
    obtain ⟨c, hc, e⟩ := outer_classes.1 g hgU ho
    rw [e]
    exact J2M.modE4_U.conj hc

theorem strictSp_J2 :
    StrictFamSp .J2 := by
  intro K _ _ ⟨e⟩
  exact StrictFix.of_mulEquiv ((e.trans nativeEquivP).symm) strictFix_J2P

end CFSG.GH74.Uniqueness.SU.K.R4
