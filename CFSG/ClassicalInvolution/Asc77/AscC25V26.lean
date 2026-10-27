module

public import CFSG.ClassicalInvolution.Asc77.AscC25V25

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups commutatorElement

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem mix25_all : Mix25 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hp : p ≠ 2 := h.hp
  have hq : 5 ≤ p ^ f := h.hs.stand.five
  have haK : a ∈ Subgroup.normalizer (K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (fix_of_isFAut h haS hF').2.2.1
  obtain ⟨e⟩ := h.hΩ.nonempty_equiv_sl2 h.hK
  by_cases hχ : fieldChar hp hq e ⟨a, haK⟩ = 1
  · exfalso
    have hnoswap : ¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K := by
      rintro ⟨c, hca, hcz, hcK⟩
      exact fieldChar_ne_one_of_swap h hp hq e ha2 hF' hca hcz hcK haK hχ
    refine false_of_mix_fusion h hp hq e haS ha2 hF' haK hχ ?_
    intro x hx
    have hax : (x⁻¹ * a * x) * z = z * (x⁻¹ * a * x) :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    have hba : (x * z * x⁻¹) * a = a * (x * z * x⁻¹) := by
      calc (x * z * x⁻¹) * a = x * (z * (x⁻¹ * a * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * a * x) * z) * x⁻¹ := by rw [hax]
        _ = a * (x * z * x⁻¹) := by group
    obtain ⟨d, hda, hbd⟩ := fs3_exists_conj_comm h haS ha2 hF' hnoswap (b := x * z * x⁻¹)
      (g := x) rfl hba
    have hda' : d⁻¹ * a = a * d⁻¹ := by
      calc d⁻¹ * a = d⁻¹ * (a * d) * d⁻¹ := by group
        _ = d⁻¹ * (d * a) * d⁻¹ := by rw [← hda]
        _ = a * d⁻¹ := by group
    have hb1a : (d⁻¹ * (x * z * x⁻¹) * d) * a = a * (d⁻¹ * (x * z * x⁻¹) * d) := by
      calc (d⁻¹ * (x * z * x⁻¹) * d) * a = d⁻¹ * ((x * z * x⁻¹) * (d * a)) := by group
        _ = d⁻¹ * ((x * z * x⁻¹) * (a * d)) := by rw [hda]
        _ = d⁻¹ * (((x * z * x⁻¹) * a) * d) := by group
        _ = d⁻¹ * ((a * (x * z * x⁻¹)) * d) := by rw [hba]
        _ = (d⁻¹ * a) * (x * z * x⁻¹) * d := by group
        _ = a * (d⁻¹ * (x * z * x⁻¹) * d) := by rw [hda']; group
    by_cases hb1 : d⁻¹ * (x * z * x⁻¹) * d = z
    · refine ⟨d⁻¹ * x, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc d⁻¹ * x * z = (d⁻¹ * (x * z * x⁻¹) * d) * (d⁻¹ * x) := by group
          _ = z * (d⁻¹ * x) := by rw [hb1]
      · calc x⁻¹ * a * x = x⁻¹ * (d * a * d⁻¹) * x := by
              have : d * a * d⁻¹ = a := by rw [hda]; group
              rw [this]
          _ = (d⁻¹ * x)⁻¹ * a * (d⁻¹ * x) := by group
    · exfalso
      have d' := twinCtx'_of_hyp25 h
      have hbN : d⁻¹ * (x * z * x⁻¹) * d ∈ Subgroup.normalizer (K' : Set G) := by
        rcases d'.conj_K hbd with h1 | h1
        · exact mem_normalizer_iff_conjSub_eq.mpr h1
        · exact absurd ⟨_, hb1a, hbd, h1⟩ hnoswap
      exact false_of_conj_normalizer' h haS ha2 hF' (b := d⁻¹ * (x * z * x⁻¹) * d)
        (g := d⁻¹ * x) (by group) hb1 hb1a hbN
  · exact Or.inr (fieldStrong25N G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' hp hq haK e hχ)

theorem mix25_nine (_h9 : p ^ f = 9) : Mix25 p f := mix25_all

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
