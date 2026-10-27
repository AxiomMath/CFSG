module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsExcKind
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsExcField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc


theorem clsExc_holds : Y10GField.ClsExc :=
  clsExc_of_fieldClosed fun _ _ hfam => canonAll_closure_field_exc hfam

end CFSG.LocalAnalysis.GLTheoremA.Y10GClsExc
