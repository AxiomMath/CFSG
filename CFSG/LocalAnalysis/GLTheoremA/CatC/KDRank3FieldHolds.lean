module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3FieldSpin
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3FieldSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3FieldLin
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3FieldUni
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3FieldGeck
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3FieldExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open TauCeti

set_option linter.unusedSectionVars false

section Holds

theorem kdRank3Field_holds : KDRank3Field := by
  refine kdRank3Field_of_forall fun d => ?_
  obtain ⟨d, hv⟩ := d
  have hrange := ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q => exact kdRank3Field_A r q hv
  | twistedA r q => exact kdRank3Field_twistedA r q hv
  | B r q =>
    have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 hrange).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact kdRank3Field_B2 q hv
    · exact kdRank3Field_B_ge3 r q hv hr3
  | C r q => exact kdRank3Field_C r q hv
  | D r q => exact kdRank3Field_D r q hv
  | twistedD r q => exact kdRank3Field_twistedD r q hv
  | E6 q => exact kdRank3Field_E6 q hv
  | E7 q => exact kdRank3Field_E7 q hv
  | E8 q => exact kdRank3Field_E8 q hv
  | F4 q => exact kdRank3Field_F4 q hv
  | G2 q => exact kdRank3Field_G2 q hv
  | twistedE6 q => exact kdRank3Field_twistedE6 q hv
  | trialityD4 q => exact kdRank3Field_trialityD4 q hv
  | suzuki m =>
    intro p _ hp2 S _ _ _ hchar _ _
    exact absurd ((LieTypeIndex.characteristic_suzuki m).symm.trans hchar).symm hp2
  | reeG2 m => exact kdRank3Field_reeG2 m hv
  | reeF4 m =>
    intro p _ hp2 S _ _ _ hchar _ _
    exact absurd ((LieTypeIndex.characteristic_reeF4 m).symm.trans hchar).symm hp2
  | tits =>
    intro p _ hp2 S _ _ _ hchar _ _
    exact absurd (LieTypeIndex.characteristic_tits.symm.trans hchar).symm hp2

end Holds

end CFSG.LocalAnalysis.GLTheoremA
