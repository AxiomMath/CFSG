module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldOrthMinus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth

open CFSG.Assembly CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField

theorem fldOrth_of_labelDict (hD : OrthLabelDict) : FldOrth := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hfld hα hlabJ hJ
  rcases hFam with ⟨ht, hr3⟩ | ⟨ht, hr2, hr3⟩
  ·
    have hcK : canonLabel labK = labK := by simp [canonLabel, ht, hr3]
    obtain ⟨hm4, hn1, K, _, _, hcard, hs, hna, e, i, f, hi, hf, hcongr, hout⟩ :=
      fieldKind_omegaPlus_data hcen ht hr3 hfld
    obtain ⟨hpn, hmodel⟩ :=
      omegaPlus_field_pComponent hm4 hn1 hp hp2 hcard hs hna e hi hf hcongr hout hα hJ
    rw [hcK, (hD ↥J labJ labK.rank (labK.n / p) hlabJ).1 hmodel]
    exact ⟨(Nat.mul_div_cancel' hpn).symm, ht, rfl⟩
  ·
    have hcK : canonLabel labK = labK := by simp [canonLabel, ht, hr2, hr3]
    obtain ⟨-, hS, hout⟩ := fieldKind_omegaMinus_model hcen ht hr2 hr3 hfld
    obtain ⟨hpn, hmodel⟩ := omegaMinus_outer_pComponent hS hp hp2 hα hout hJ
    rw [hcK, (hD ↥J labJ labK.rank (labK.n / p) hlabJ).2 hmodel]
    exact ⟨(Nat.mul_div_cancel' hpn).symm, ht, rfl⟩

theorem fldOrth_holds :
    FldOrth :=
  fldOrth_of_labelDict orthLabelDict_holds

end CFSG.LocalAnalysis.GLTheoremA.Y10GFldOrth
