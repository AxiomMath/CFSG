module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Reduce
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Uniq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamPSU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamSp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamG2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamF4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamTwE6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamTri
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LieType.Catalog.Realization

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG CFSG.Blueprint CFSG.Open CFSG.ComponentClassification

section


theorem cl24_tracked_all : ∀ τ, Cl24TrackedFamily τ := by
  intro τ
  cases τ
  · exact cl24_family_PSL.tracked
  · exact cl24_family_PSU.tracked
  · exact cl24_family_PSp.tracked
  · exact cl24_family_POmegaOdd.tracked
  · exact cl24_family_POmegaPlus.tracked
  · exact cl24_family_POmegaMinus.tracked
  · exact cl24_tracked_G2
  · exact cl24_family_F4.tracked
  · exact cl24_family_E6.tracked
  · exact cl24_family_E7.tracked
  · exact cl24_family_E8.tracked
  · exact cl24_family_twistedE6.tracked
  · exact cl24_tracked_trialityD4
  · exact cl24_tracked_twistedB2
  · exact cl24_tracked_twistedG2
  · exact cl24_tracked_twistedF4
  · exact cl24_tracked_Tits

theorem a2l_cl2_holds : HypA2.ClosureFieldExp :=
  a2l_cl2_of_tracked CatLeafProof.lieOrderFormulasInput
    (fun G _ t n p f h => (LieType.Catalog.lieModel_finite_simple G t n p f h).2.2)
    cl24_tracked_all (a2l_cl2_fieldUnique3 CatLeafProof.lieOrderFormulasInput)

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
