module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.LeavesTwoK
public import CFSG.CGT.A8S.Final
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection

public section

namespace CFSG.CGT.PushingUpLit


theorem aschbacherTwoK_solomonK_holds
    :
    AschbacherTheoremTwoK ∧ SolomonAlternatingBlockK := by
  have hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models :=
    @CFSG.Milestones.cl_lit_classical_involution_theorem_models
  have hQuat : SolKNA.QuaternionInspectionLie :=
    SolKNA.quaternionInspectionLie_of_cit3
      (SolKNA.cit3Inductive_of_citInputs CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
      (SolKNA.tightLiftSimple_of_citInputs CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
  exact CFSG.AGLEmbeddingD2.aschbacherTwoK_solomonK_of_remaining CFSG.CGT.A8S.a8SylowInput
    (SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz hCIT hQuat
      SolKNA.szFpfSimpleNatural_of_certificate)

theorem aschbacherTheoremTwoK_holds
    : AschbacherTheoremTwoK :=
  aschbacherTwoK_solomonK_holds.1

theorem solomonAlternatingBlockK_holds
    : SolomonAlternatingBlockK :=
  aschbacherTwoK_solomonK_holds.2

end CFSG.CGT.PushingUpLit
