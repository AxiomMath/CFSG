module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6PSp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6A8Gen4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCat81E6Q3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem cf81E6Cls_of_psp
    (h : CF81E6ClsPSp) :
    CF81E6Cls := by
  intro K₀ _ _ p f hp hp2 hf hS c
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.1 h3
    exact Cat81Q3.cls_three hS h3 c
  · exact h K₀ p f hp hp2 hf h3 (lieModel_of_isSec8Socle hS h3) c

theorem cf81E6Out_of_psp
    (h : CF81E6OutPSp) : CF81E6Out := by
  intro K₀ _ _ p f hp hp2 hf hS α hα
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.1 h3
    exact Cat81Q3.out_three hS h3 hα
  · exact h K₀ p f hp hp2 hf h3 (lieModel_of_isSec8Socle hS h3) α hα

theorem cf81E6Fld_of_psp
    (h : CF81E6FldPSp) : CF81E6Fld := by
  intro K₀ _ _ p f hp hp2 hf hS α hα S₀ hS₀ hle ψ hψ hψN
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.1 h3
    exact (hψN ((Cat81Q3.innA_eq_top hS h3 hα).symm ▸ mem_top ψ)).elim
  · exact h K₀ p f hp hp2 hf h3 (lieModel_of_isSec8Socle hS h3) α hα S₀ hS₀ hle ψ hψ hψN

theorem cf81E6Sect_of_psp
    (h : CF81E6SectPSp) : CF81E6Sect := by
  intro K₀ _ _ p f hp hp2 hf hS c R hR h2
  rcases hS with hL | ⟨rfl, rfl, ⟨e⟩⟩
  · exact h K₀ p f hp hp2 hf hL c R hR h2
  · refine ⟨Cat81A8.gen4_mulAut e R h2, ?_⟩
    rw [Cat81Q3.card_D_three (Or.inr ⟨rfl, rfl, ⟨e⟩⟩) (by norm_num) c]
    exact (Cat81A8.card_le_of_isPGroup e h2).trans (by norm_num)

end CFSG.ComponentClassification.GSThmB
