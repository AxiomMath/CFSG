module

public import CFSG.CGT.Timmesfeld75.FinalReduced3
public import CFSG.CGT.Timmesfeld75.AschbacherNoPolarDischarge
public import CFSG.CGT.Timmesfeld75.Sec3IsoParts

public section

namespace CFSG.CGT.Timmesfeld75

structure RemainingLiteratureInputs : Prop where
  aschbacherTheoremOne : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne
  benderCenter : BenderCenterInput
  unitaryTwoGeneration : UnitaryTwoGenerationInput

theorem ReducedLiteratureInputs.of_remaining
    (L : RemainingLiteratureInputs) :
    ReducedLiteratureInputs where
  aschbacherNoPolar := aschbacherNoPolarInput_of_repo
  aschbacherTheoremOne := L.aschbacherTheoremOne
  benderCenter := L.benderCenter
  unitaryTwoGeneration := L.unitaryTwoGeneration

theorem lemma214_of_remaining
    (L : RemainingLiteratureInputs) : Lemma214 :=
  lemma214_of_literature (LiteratureInputs.of_reduced (ReducedLiteratureInputs.of_remaining L))

theorem section3IsoInput_of_remaining
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) : Section3IsoInput :=
  section3IsoInput_of_parts (lemma214_of_remaining L) hSz hD

theorem theoremA_of_parts
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) (P : CoreStepInputs) : TheoremAStmt :=
  theoremA_of_core_steps (ReducedLiteratureInputs.of_remaining L)
    (section3IsoInput_of_remaining L hSz hD) P

theorem node_of_parts
    (L : RemainingLiteratureInputs) (hSz : Section3SzInput)
    (hD : Section3DihedralInput) (P : CoreStepInputs) : NodeStatement :=
  node_of_core_steps (ReducedLiteratureInputs.of_remaining L)
    (section3IsoInput_of_remaining L hSz hD) P

end CFSG.CGT.Timmesfeld75
