module

public import CFSG.CGT.Hall82.TheoremB
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
public import CFSG.RankThree.PartOne.S12.SolInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main

public section

namespace CFSG.CGT.Hall82

theorem lit316Hall_of_tight
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) :
    CFSG.RankThree.PartTwo.Sec19.Lit316Hall :=
  lit316Hall_of_setting CFSG.CGT.PushingUpLit.LIT.Foote.footeNonsolvableSimple_holds
    fun _ _ _ _ _ S => S.inCatalog CFSG.RankThree.PartTwo.Sec19.SolSeven.nodeStatement_holds hSTT

theorem lit316Hall_holds :
    CFSG.RankThree.PartTwo.Sec19.Lit316Hall :=
  lit316Hall_of_tight (CFSG.RankThree.PartOne.SolIn.solomonTimmesfeldTight_of_inputs
      (CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
          CFSG.ComponentClassification.Foote5.HallGen.hallQ8Residual)
      (⟨PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz
          CFSG.Milestones.cl_lit_classical_involution_theorem_models
          (PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
              (PushingUpLit.SolKNA.cit3Inductive_of_citInputs
                  CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
              (PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
                  CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))
          PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate,
          PushingUpLit.SolKR2.solomonTimmesfeldMainRankTwo_holds⟩ :
          PushingUpLit.SolKAb.SolomonTimmesfeldMainResidue))

end CFSG.CGT.Hall82
