module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eHolds
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

theorem harris82Lemma51eOdd_holds :
    Harris82Lemma51eOdd := by
  intro X _ _ _ p hp hp2 hX z hz J hJ _ r hr
  exact P51e.not_isCoverOf_holds X hp hp2 hX hz hJ hr

end CFSG.ComponentClassification.HarrisLit.T1
