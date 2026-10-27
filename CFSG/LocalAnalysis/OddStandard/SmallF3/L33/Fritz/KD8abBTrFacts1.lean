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

theorem tr_facts_1a :
    ((H4Zof (0, 2)).take 64).all (trCheck (0, 2)) = true := by
  decide +kernel

theorem tr_facts_1b :
    ((H4Zof (0, 2)).drop 64).all (trCheck (0, 2)) = true := by
  decide +kernel

theorem tr_facts_2a :
    ((H4Zof (0, 10)).take 64).all (trCheck (0, 10)) = true := by
  decide +kernel

theorem tr_facts_2b :
    ((H4Zof (0, 10)).drop 64).all (trCheck (0, 10)) = true := by
  decide +kernel

theorem tr_facts_3a :
    ((H4Zof (1, 0)).take 64).all (trCheck (1, 0)) = true := by
  decide +kernel

theorem tr_facts_3b :
    ((H4Zof (1, 0)).drop 64).all (trCheck (1, 0)) = true := by
  decide +kernel

theorem tr_facts_4a :
    ((H4Zof (1, 8)).take 64).all (trCheck (1, 8)) = true := by
  decide +kernel

theorem tr_facts_4b :
    ((H4Zof (1, 8)).drop 64).all (trCheck (1, 8)) = true := by
  decide +kernel

end MB

end Sec8

end CFSG.OddStandard.SmallF3.L33.KD
