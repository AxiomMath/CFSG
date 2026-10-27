module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GSurvBr

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.I107G

theorem survivorLabelCat_holds :
    SurvivorLabelCat := by
  intro lab _ hsurv Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  simp only [survivor107] at hsurv
  rcases hsurv with ⟨hn, (⟨(rfl | rfl), rfl⟩ | ⟨rfl, (rfl | rfl)⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl)⟩ |
    ⟨rfl, rfl, rfl⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_sp6_recipe (hK.trans (by norm_num))⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_sp6_recipe (hK.trans (by norm_num))⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_u4_recipe (hK.trans (by norm_num))⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_u5_recipe (hK.trans (by norm_num))⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_u4_recipe (hK.trans (by norm_num))⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_d4_recipe (hK.trans (by norm_num))⟩
  ·
    subst hn
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_isList107_of
      (fun i hi => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hi))))) (catalogIs_td4_recipe hK)⟩
  ·
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQK⟩ := hQ
    exact ⟨K, hf, hfin, hK, hQK, catalogIs_u3_recipe (hK.trans (by norm_num))⟩

end CFSG.LocalAnalysis.GLTheoremA

end
