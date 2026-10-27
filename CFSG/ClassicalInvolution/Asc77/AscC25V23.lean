module

public import CFSG.ClassicalInvolution.Asc77.AscC25V22
public import CFSG.ClassicalInvolution.Asc77.AscC25V19
public import CFSG.ClassicalInvolution.Asc77.AscC25V8
public import CFSG.ClassicalInvolution.Asc77.AscC25V21

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups commutatorElement

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem fus25 : Fus25 p f := by
  intro h9 G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF hnoswap x hx
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hax : (x⁻¹ * a * x) * z = z * (x⁻¹ * a * x) :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hba : (x * z * x⁻¹) * a = a * (x * z * x⁻¹) := by
    calc (x * z * x⁻¹) * a = x * (z * (x⁻¹ * a * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * a * x) * z) * x⁻¹ := by rw [hax]
      _ = a * (x * z * x⁻¹) := by group
  obtain ⟨d, hda, hbd⟩ := fs_exists_conj_comm h h9 haS ha2 hF hnoswap (b := x * z * x⁻¹)
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
    exact false_of_conj_normalizer h h9 haS ha2 hF (b := d⁻¹ * (x * z * x⁻¹) * d)
      (g := d⁻¹ * x) (by group) hb1 hb1a hbd hnoswap

theorem mix25_proved (h9 : p ^ f ≠ 9) : Mix25 p f := mix25_of_ne_nine h9 fus25

theorem c25_16inv_of_ff (h11 : C25_11 p f) (hmix9 : p ^ f = 9 → Mix25 p f) (hff : FF25 p f) :
    T7U.C25_16inv p f := by
  by_cases h9 : p ^ f = 9
  · exact c25_16inv_of_parts h11 (hmix9 h9) hff
  · exact c25_16inv_of_parts h11 (mix25_proved h9) hff

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
