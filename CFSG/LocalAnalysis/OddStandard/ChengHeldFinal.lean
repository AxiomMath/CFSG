module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldMain
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl1CertN
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2Zero
public import CFSG.LocalAnalysis.OddStandard.ChengHeldExcl2OneMain

public section

namespace CFSG.OddStandard.ChengHeld

theorem l34EvenSylowStepBal_holds :
    CFSG.OddStandard.L34EvenSylowStepBal :=
  l34EvenSylowStepBal_of_exclusions
    (fun hα c hb hc _ hg hact hk => Chart4.excl_QS hα c hb.toHyp hc hg hact hk)
    (fun hα c hb hc _ hg hact hk => Chart4.excl_graph hα c hb.toHyp hc hg hact hk)
    (fun hα c hb hc _ _ _ hk => Chart4.excl_field_cert hα c hb.toHyp hc hk)
    (fun _ c hb hc _ hg hact hα0 hk => by
      subst hα0
      exact Chart4.excl_both_zero hb hc c hg hact hk)
    (fun _ c hb hc _ hg hact hα1 hk => by
      subst hα1
      exact Chart4.excl_both_one hb hc c hg hact hk)

end CFSG.OddStandard.ChengHeld
