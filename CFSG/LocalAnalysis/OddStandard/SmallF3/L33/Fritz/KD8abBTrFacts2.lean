module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBTrData

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8
open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB
open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem tr_facts_5a :
    ((H4Zof (2, 2)).take 64).all (trCheck (2, 2)) = true := by
  decide +kernel

theorem tr_facts_5b :
    ((H4Zof (2, 2)).drop 64).all (trCheck (2, 2)) = true := by
  decide +kernel

theorem tr_facts_6a :
    ((H4Zof (2, 10)).take 64).all (trCheck (2, 10)) = true := by
  decide +kernel

theorem tr_facts_6b :
    ((H4Zof (2, 10)).drop 64).all (trCheck (2, 10)) = true := by
  decide +kernel

theorem tr_facts_7a :
    ((H4Zof (3, 0)).take 64).all (trCheck (3, 0)) = true := by
  decide +kernel

theorem tr_facts_7b :
    ((H4Zof (3, 0)).drop 64).all (trCheck (3, 0)) = true := by
  decide +kernel

theorem tr_facts_8a :
    ((H4Zof (3, 8)).take 64).all (trCheck (3, 8)) = true := by
  decide +kernel

theorem tr_facts_8b :
    ((H4Zof (3, 8)).drop 64).all (trCheck (3, 8)) = true := by
  decide +kernel

end MB

end Sec8

end CFSG.OddStandard.SmallF3.L33.KD
