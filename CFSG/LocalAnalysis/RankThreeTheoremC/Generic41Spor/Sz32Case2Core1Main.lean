module

import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1CaseA
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1One
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Cfg
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Syl
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1End
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2CoreBNotInv
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Main

variable {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}

theorem szh1_caseB (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five) (hI122 : KFactI122Five)
    (hI713 : KFactI713Out) (hcomp : ∃ L : Subgroup Y, IsComponentOf L ⊤) : False := by
  obtain ⟨L₁, h₁⟩ := hcomp
  by_cases hall : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L₁
  · exact szh1_one_comp_false hY hI6103 hI122 h₁ hall
  · push Not at hall
    obtain ⟨L₂, h₂, hne⟩ := hall
    obtain ⟨t, ht⟩ := szh1_exists_two_config hY hI6103 h₁ h₂ hne.symm
    have hs := szh1_two_sylow hY hI713 ht
    exact szh1_two_numeric hY ht hs (szh1_two_not_inverting' hY hI713 ht hs)

theorem szh1_Pb_normal (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five) (hI122 : KFactI122Five)
    (hI713 : KFactI713Out) : ∀ g : Y, ∀ t ∈ Pb, g * t * g⁻¹ ∈ Pb := by
  by_cases hcomp : ∃ L : Subgroup Y, IsComponentOf L ⊤
  · exact (szh1_caseB hY hI6103 hI122 hI713 hcomp).elim
  · push Not at hcomp
    exact szh1_caseA hY hcomp

end Main

theorem sz32_case2_core' {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}
    (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five) (hI122 : KFactI122Five)
    (hI713 : KFactI713Out) : a ∈ pCoreOf 5 (⊤ : Subgroup Y) := by
  have hnorm := szh1_Pb_normal hY hI6103 hI122 hI713
  obtain ⟨S, hS⟩ := hY.sylow
  have hp : IsPGroup 5 (Pb : Subgroup Y) := by
    rw [← hS]; exact S.isPGroup'
  have hle : Pb ≤ pCoreOf 5 (⊤ : Subgroup Y) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 5 le_top ?_ hp
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm g h hh, fun hh => ?_⟩
    have h1 := hnorm g⁻¹ _ hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1
  exact hle hY.pres.a_mem

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
