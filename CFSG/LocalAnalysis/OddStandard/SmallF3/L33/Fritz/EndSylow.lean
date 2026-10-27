module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDOut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDKDExists
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Sec6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abACase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cMain

public section

namespace CFSG.OddStandard.SmallF3.L33

open Subgroup CFSG.ComponentClassification.HSFLit CFSG.OddStandard.SmallF3.L33.KD

theorem exists_ghRel_sylow
    (hH : HaradaInput) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) {t : X} {L : Subgroup X} (h : FritzHyp X t L) :
    ∃ (P : Sylow 2 X) (z l α₁ α₂ α₃ α₄ x y a : X), GHRel z l α₁ α₂ α₃ α₄ x y a ∧
      Subgroup.closure ({z, l, α₁, α₂, α₃, α₄, x, y, a} : Set X) = P ∧
        Nat.card (P : Subgroup X) = 512 := by
  obtain ⟨ctx⟩ := exists_sdCtx hH h
  have hnot : ¬ SectRank4 X := h.not_sectRank4
  obtain ⟨C', S, T₁, h4T⟩ := fritzKDSection4 hH X hnonab hnot t L ctx.A ctx.C ctx.kdBase
  obtain ⟨⟨D₁⟩, ⟨D₂⟩⟩ := fritzKDSection6 hH X hnonab hnot t L ctx.A C' S T₁ h4T
  by_cases h78 : D₁.q0 = .e4q8 ∨ D₁.q0 = .exceptional ∨ D₂.q0 = .e4q8 ∨ D₂.q0 = .exceptional
  · exact (fritzKDSection7 hH X hnonab hnot t L ctx.A C' S T₁ h4T D₁ D₂ h78).elim
  · push Not at h78
    obtain ⟨h1, h2, h3, h4'⟩ := h78
    have hD₁ : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic ∨ D₁.q0 = .extraspecial := by
      cases hq : D₁.q0 <;> simp_all
    have hD₂ : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic ∨ D₂.q0 = .extraspecial := by
      cases hq : D₂.q0 <;> simp_all
    by_cases hc : D₁.q0 = .extraspecial ∧ D₂.q0 = .extraspecial
    · exact KD8c.fritzKDSection8c hH X hnonab hnot t L ctx.A C' S T₁ h4T D₁ D₂ hc.1 hc.2
    · exact (KD8ab.fritzKDSection8ab_of_cases KD8ab.caseA KD8abB.caseB hH X hnonab hnot t L ctx.A
        C' S T₁ h4T D₁ D₂ hD₁ hD₂ hc).elim

end CFSG.OddStandard.SmallF3.L33
