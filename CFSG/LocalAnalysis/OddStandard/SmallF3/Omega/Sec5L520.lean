module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma520_of (h517 : Asc82Lemma517) (h518b : Asc82Lemma518b) (h519 : Asc82Lemma519)
    (hE : Asc82End520) (hC : Asc82CorIIIq) : Asc82Lemma520 := by
  intro G _ _ t L S z r B A K₁ K₂ h c
  obtain ⟨p, n, hp, K, hn, hq, hK⟩ := hE h517 h518b h519 G t L S z r B A K₁ K₂ h c
  exact (hC G t L c.toSec3SettingLB z K p n c.pocket.1 hn hq hK).elim

end CFSG.OddStandard.SmallF3.Omega
