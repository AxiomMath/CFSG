module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResAll
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResTLTwo

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false

section Final

theorem excResidual_f4_of (hO : ExcTLOther Tag.F4) :
    ExcResidual FamF4 := excResidual_f4 (excTLInner_of_ne_G2 (by decide))
      (excTLInnerTwo_of_ne_G2 (by decide)) hO

theorem excResidual_e6Good_of (hO : ExcTLOther Tag.E6) :
    ExcResidual FamE6Good := excResidual_e6Good (excTLInner_of_ne_G2 (by decide))
      (excTLInnerTwo_of_ne_G2 (by decide)) hO

theorem excResidual_twE6Good_of (hO : ExcTLOther Tag.E6) :
    ExcResidual FamTwE6Good := excResidual_twE6Good (excTLInner_of_ne_G2 (by decide))
      (excTLInnerTwo_of_ne_G2 (by decide)) hO

theorem excResidual_e7_of (hO : ExcTLOther Tag.E7) :
    ExcResidual FamE7 := excResidual_e7 (excTLInner_of_ne_G2 (by decide))
      (excTLInnerTwo_of_ne_G2 (by decide)) hO

theorem excResidual_e8_of (hO : ExcTLOther Tag.E8) :
    ExcResidual FamE8 := excResidual_e8 (excTLInner_of_ne_G2 (by decide))
      (excTLInnerTwo_of_ne_G2 (by decide)) hO

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I1431
