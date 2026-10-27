module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusF6
public import Certificates.Certificate442351

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzFus

theorem fzFus_facts :
    Fz722c ∧ ClassFact ∧ RowsFact ∧ SubsFact := by
  obtain ⟨hC, hR, hS, hN⟩ := fusCheck_sound Certificates.certificate442351
  exact ⟨fz722c_of (fzNoPointedEmbedZ3_of fzfus_pairAtR (fzfus_noPairAtZ3 hN)), hC, hR, hS⟩

end CFSG.OddStandard.SmallF3.FritzII
