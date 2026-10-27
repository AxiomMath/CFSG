module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP11g1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP11g2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP11g3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP11gU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification

theorem fzSylowOfClosure_of_hall
    (hgold : Asc76X.GoldschmidtTheoremA) : FzSylowOfClosure := by
  intro G _ _ z T Y R hz hT hTz hRq hzR hRT hTYR hYR hYRz hcl
  obtain ⟨-, -, hcomm⟩ := fz_g_q8_facts hz hRq hzR
  have hRC : R ≤ centralizer ({z} : Set G) := hRT.trans hTz
  have hSyl := fz_bar_sylow hT hTz
  have hle := fz_bar_le (z := z) hRT
  have hcard := fz_bar_card hz hRq hzR hRC
  have hel := fz_bar_elemAbelian hz hRq hzR hRC
  have hstrong := fz_bar_strong hzR hRT hTz hcl
  have hweak := fz_weak_of_strong hstrong
  rcases Asc76X.Hall32.caseA hgold hSyl hle hcard hel hweak hstrong with h | h
  · exact fz_relIndex_of_bar_sylow hzR hRC h
  · exact (fz_not_u34 hSyl hle hcard hel.2 (fz_bar_comm hzR hRT hTz hcomm hTYR hYR hYRz) h).elim

end CFSG.OddStandard.SmallF3.FritzII
