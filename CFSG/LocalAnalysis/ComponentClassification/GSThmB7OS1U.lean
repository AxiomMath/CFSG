module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma517
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Prop
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem normalizer_B0_le_U {h : Hyp52 X} {y b : X} (hb : Lemma61Case2 h y b) :
    h.S ⊓ h.secG0 y ≤ centralizer ({b} : Set X) := by
  obtain ⟨hb2, -, hU2, hbB0, -, -, -⟩ := hb
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hbB : b ∈ h.B := (mem_inf.mp hbB0).1
  have hbS : b ∈ h.S := h.B_le_S hbB
  have haa : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  have hba : b * h.a = h.a * b := h.comm_a hbS
  have hbU2 : b ∈ h.upperS 2 := by
    have : b ∈ h.upperP 2 := by rw [hU2]; exact subset_closure (by simp)
    exact (mem_inf.mp this).1
  intro r hr
  obtain ⟨hrS, hrN⟩ := mem_inf.mp hr
  have hrb : r * b * r⁻¹ ∈ h.upperP 2 := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (h.commutator_mem_upperS hbU2 hrS).2
      have h2 : r * b * r⁻¹ = ⁅r, b⁆ * b := by
        rw [commutatorElement_def]
        calc r * b * r⁻¹ = r * b * r⁻¹ * (b⁻¹ * b) := by group
          _ = r * b * r⁻¹ * b⁻¹ * b := by group
      rw [h2]
      exact mul_mem (h.upperS_mono (by norm_num) h1) hbU2
    · exact h.B_le_P ((mem_inf.mp ((mem_normalizer_iff.mp hrN b).mp hbB0)).1)
  rw [hU2] at hrb
  have hrbB : r * b * r⁻¹ ∈ h.B := (mem_inf.mp ((mem_normalizer_iff.mp hrN b).mp hbB0)).1
  rw [mem_centralizer_singleton_iff]
  rcases Six.mem_closure_pair_cases haa hbb hba hrb with h1 | h1 | h1 | h1
  · exfalso
    have : b = 1 := by
      calc b = r⁻¹ * (r * b * r⁻¹) * r := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  · exact absurd (h1 ▸ hrbB) h.a_not_mem_B
  · calc r * b = (r * b * r⁻¹) * r := by group
      _ = b * r := by rw [h1]
  · exfalso
    apply h.a_not_mem_B
    have h2 : h.a = r * b * r⁻¹ * b := by rw [h1, mul_assoc, hbb, mul_one]
    rw [h2]
    exact mul_mem hrbB hbB

end Seven

end CFSG.ComponentClassification.GSThmB
