module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatSporadic
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2
public import CFSG.CGT.PushingUpLit.SolKNA.SzAbelianFinal

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)

section Top

set_option linter.unusedSectionVars false


theorem rankGe2_holds_of (hS : SzFpfSimpleNatural) : SolomonTimmesfeldMainRankGe2 :=
  rankGe2_of_szAbelian (lemma18SzAbelian_of_simple hS)

theorem solomonTimmesfeldMainNonAbelian_of_cit_lie_sz
    (hCIT : ClassicalInvolutionTheoremModels) (hL : QuaternionInspectionLie)
    (hS : SzFpfSimpleNatural) :
    CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainNonAbelian :=
  solomonTimmesfeldMainNonAbelian_of_lie_inputs hCIT hL
      (rankGe2_of_szAbelian (lemma18SzAbelian_of_simple hS))

end Top

end CFSG.CGT.PushingUpLit.SolKNA
