module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUStep

public section

namespace CFSG.ComponentClassification.TBLit

theorem l34FieldUnitaryMaximalStep_of_griessSolomon (hGS : GSLit.GriessSolomonInput) :
    L34FieldUnitaryMaximalStep := by
  intro X _ _ _ hnonab hK hz hU b y _ K hT _ hL34 _ _ _ _ _
  exact (hGS X hnonab hK hz hU ⟨b, y, K, hT, Or.inr hL34⟩).elim

end CFSG.ComponentClassification.TBLit
