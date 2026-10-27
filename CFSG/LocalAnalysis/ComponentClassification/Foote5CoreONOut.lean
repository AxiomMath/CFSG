module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreSporD
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG CFSG.Blueprint

theorem oNanOuterCardLeTwo_holds :
    ONanOuterCardLeTwo :=
  Nat.le_of_dvd (by norm_num) (Sporadic.SteinbergBI.cti_on_outer_order_divides_two
    ⟨(MulEquiv.refl _ : NativeSporadic.Carrier .ONan ≃* NativeSporadic.ON)⟩)

end CFSG.ComponentClassification.Foote5
