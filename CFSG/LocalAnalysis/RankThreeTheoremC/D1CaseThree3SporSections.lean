module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporRank
import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.RankThree.PartOne (exists_section_of_quotient_subgroup)

variable {G : Type} [Group G] [Finite G]

theorem false_of_mem_sectionExcluded3 (hsec : SporSectionFacts3)
    (hS : CFSG.Open.evenRank G = 3) {H : Subgroup G} (N : Subgroup H) [N.Normal]
    {K : Subgroup (H ⧸ N)} (hKsimple : IsSimpleGroup (K ⧸ Subgroup.center K))
    (hKnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  obtain ⟨b⟩ := hsec.bridge s
  obtain ⟨H₁, H₂, hH₂, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup N K
  have h4 : 4 ≤ CFSG.Assembly.evenRank H := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hsec.fi22 H H₁ H₂ ⟨φ.trans (e.trans b.symm)⟩
    · exact hsec.fi23 H H₁ H₂ ⟨φ.trans (e.trans b.symm)⟩
    · exact hsec.fi24Prime H H₁ H₂ ⟨φ.trans (e.trans b.symm)⟩
    · exact hsec.babyMonster H H₁ H₂ ⟨φ.trans (e.trans b.symm)⟩
    · exact hsec.monster H H₁ H₂ (K ⧸ Subgroup.center K) hKnonab ⟨φ⟩ ⟨e.trans b.symm⟩
  have h3 : CFSG.Assembly.evenRank G = 3 := hS
  have hle := CFSG.RankThree.PartTwo.evenRank_subgroup_le H
  omega

theorem noExcludedSection3_of_sections (hsec : SporSectionFacts3)
    (hS : CFSG.Open.evenRank G = 3) : NoExcludedSection3 G := by
  intro H N _ K hK s hs ⟨e⟩
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  exact false_of_mem_sectionExcluded3 hsec hS N hK.2
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK) hs e

theorem KFactsA3.of_sections (hβ : KFactBetaRank2) (hsec : SporSectionFacts3)
    (hS : CFSG.Open.evenRank G = 3) : KFactsA3 G :=
  ⟨hβ, noExcludedSection3_of_sections hsec hS⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
