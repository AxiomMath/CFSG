module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthFC
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFC

open CFSG.Open

theorem orthFieldComps_holds : OrthFieldComps :=
  fun _ _ _ _ ht hn hS _ hβ hout => OrthFix.orthField_comps ht hn hS hβ hout

theorem orthTwoInner_holds : OrthTwoInner :=
  fun _ _ _ _ ht hn hS _ hβ => OrthFix.orthTwo_inner ht hn hS hβ

theorem bal207OrthFirstClaim_of_innerCases (hGA : GriessAllModelsStatement) (hC : OrthInnerCases)
    (hD : OrthBlockFrame) (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207OrthFirstClaim G :=
  bal207OrthFirstClaim_of_cases hGA hC hD orthFieldComps_holds orthTwoInner_holds G

end CFSG.HardMathSupport.Dickson.Bal207.OrthFC

end
