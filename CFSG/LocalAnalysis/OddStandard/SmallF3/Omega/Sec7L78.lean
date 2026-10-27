module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78R
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Cases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma78_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h76 : Asc82Lemma76)
    (h61 : Asc82Lemma61) (hP : Asc82Tab6P) (hOm5 : Sec8T84FactOm5Out) (hE : Asc82E16Good)
    (h77a : Asc82Lemma77a) (h77b : Asc82Lemma77b) : Asc82Lemma78 := by
  intro G _ _ t L S z g B hc
  by_contra hne
  obtain ⟨r, hrA, hr1, hrt, hrs, hrN₁, hrN₂⟩ := sec7l78_exists_r h36 h72 h76 hP h77a h77b hc hne
  obtain ⟨P', hsL', hMeq⟩ := sec7l78_sideL' h36 h72 h76 hP h77a hc
  have hsL := sec7l78_sideL h36 h76 hP hc
  obtain ⟨K, hW₁, hW₂, hK⟩ :=
    sec7l78_exists_K h36 h61 hP hOm5 hc hsL hsL' hrA hr1 hrt hrs hrN₁ hrN₂
  obtain ⟨hBD, hW⟩ : _ ∧ _ := hK.elim
    (fun hKL => sec7l78_BD_eq_of_le hP hsL hsL' hKL.1 hKL.2 hW₁ hW₂)
    (fun hK6 => sec7l78_BD_eq_om6 hP hE hsL hsL' hK6 hW₁ hW₂)
  refine sec7l78_finish hP hsL hsL' hBD hW ?_
  obtain ⟨n, hn, htn⟩ := h77b G t L S z g B hc
  exact ⟨n, hMeq ▸ hn, htn⟩

end CFSG.OddStandard.SmallF3.Omega
