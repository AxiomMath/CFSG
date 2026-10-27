module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Three
public import CFSG.CGT.PushingUpLit.LIT.Foote.L54OneEnd
public import CFSG.CGT.PushingUpLit.LIT.Foote.TheoremA

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement)

theorem lemma_5_4
    (h3 : Theorem3Statement) : Lemma54 := by
  intro G _ _ M J z₀ c hz₀
  by_contra hnot
  have hth : Three M J := Three.of_not_twoOrbit c hnot
  by_cases hfus : ∃ g : G, g ∉ M ∧ ∃ t ∈ rightConjugate J g, t ∈ M ∧ t ≠ 1 ∧ t * t = 1
  · obtain ⟨g, hg, t₀, ht₀J, ht₀M, ht₀1, ht₀2⟩ := hfus
    exact c.part_two h3 footeTheoremA hz₀ hth hg ht₀J ht₀M ht₀1 ht₀2
  · refine c.part_one footeTheoremA hz₀ hth ?_
    intro h hh t htJ htMh ht2
    by_contra ht1
    apply hfus
    have htM : h * t * h⁻¹ ∈ M := (mem_rightConjugate_iff _ _ _).1 htMh
    refine ⟨h⁻¹, fun hmem => hh (by simpa using M.inv_mem hmem), h * t * h⁻¹, ?_, htM, ?_, ?_⟩
    · rw [mem_rightConjugate_iff]
      have e : h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ = t := by group
      rw [e]
      exact htJ
    · intro h1
      apply ht1
      have : t = h⁻¹ * (h * t * h⁻¹) * h := by group
      rw [this, h1]
      group
    · calc h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ := by group
        _ = 1 := by rw [ht2]; group

end CFSG.CGT.PushingUpLit.LIT.Foote
