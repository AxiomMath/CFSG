module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenSuzukiRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem evenLieOuterTwoComponentsInput_holds :
    EvenLieOuterTwoComponentsInput :=
  evenLieOuterTwoComponentsInput_of_families fun τ => by
    cases τ
    exacts [evenOuterFamilyInput_PSL_holds, evenOuterFamilyInput_PSU, evenOuterFamilyInput_PSp,
      evenOuterFamilyInput_POmegaOdd, evenOuterFamilyInput_POmegaPlus,
      evenOuterFamilyInput_POmegaMinus, evenOuterFamilyInput_G2, evenOuterFamilyInput_F4,
      evenOuterFamilyInput_E6, evenOuterFamilyInput_E7, evenOuterFamilyInput_E8,
      evenOuterFamilyInput_twistedE6, evenOuterFamilyInput_trialityD4,
      evenOuterFamilyInput_twistedB2, evenOuterFamilyInput_twistedG2,
      evenOuterFamilyInput_twistedF4, evenOuterFamilyInput_Tits]

end CFSG.ComponentClassification.CatLeafProof
