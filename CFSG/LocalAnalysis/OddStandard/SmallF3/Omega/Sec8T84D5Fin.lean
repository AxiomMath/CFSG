module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D4Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D5Asm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma811K_of (F : Sec8T84Base) (h89 : Asc82Lemma89) (h810 : Asc82Lemma810K)
    (hMS : Sec8T84ModelSylow) : Asc82Lemma811K :=
  asc82Lemma811K_of_split F h89 h810 (sec8t84d5_splitK F hMS)

end CFSG.OddStandard.SmallF3.Omega
