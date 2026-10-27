module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutAbP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutL2Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FactAutAb_of_cert :
    Asc82FactAutAb := by
  intro G _ _ I hI hmodel Y hYN hYC hp hc
  rcases hmodel with hK | hK
  · exact card_le_16_of_psp43_quotient hI hK hYN hYC hp hc
  · have hs : IsSimpleGroup (↥I ⧸ oddCore ↥I) := by
      have hmodel := hK.statedClassicalModel_of_ne_zero (by norm_num)
      exact (CFSG.LieType.Simplicity.fam_classical_converse (↥I ⧸ oddCore ↥I)
        ⟨_, _, 3, _, hmodel⟩).2.2
    exact card_le_of_aut_embedding hI hs hYN hYC hp hc fun X hX hXc =>
      aut_psl281_abelian_two_le_16 hK X hX hXc

end CFSG.OddStandard.SmallF3.Omega
