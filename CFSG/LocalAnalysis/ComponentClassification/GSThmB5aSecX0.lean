module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecSyl

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem IsX0.conj_mem_Q (hy : h.IsX0 y) {q : X} (hq : q ∈ h.Q) : y * q * y⁻¹ ∈ h.Q := by
  have h1 : ⁅y, q⁆ ∈ h.T := hy.2.2.2 q (mem_inf.mp hq).1
  rw [show y * q * y⁻¹ = ⁅y, q⁆ * q by rw [commutatorElement_def]; group]
  exact mul_mem (mem_inf.mp h1).1 hq

theorem IsX0.secCond (hy : h.IsX0 y) : h.SecCond y := by
  refine ⟨hy.1, hy.2.1, hy.2.2.1, fun q hq => ?_, ?_⟩
  · apply B5a.mem_normalizer_of_map_le
    rintro _ ⟨z, hz, rfl⟩
    rw [secB0] at hz ⊢
    obtain ⟨hzB, hzy⟩ := mem_inf.mp hz
    have hqN : q ∈ normalizer (h.B : Set X) := (mem_inf.mp hq).2
    have hyq : y * q * y⁻¹ ∈ normalizer (h.B : Set X) := (mem_inf.mp (hy.conj_mem_Q hq)).2
    show q * z * q⁻¹ ∈ h.B ⊓ conjugate h.B y
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hqN z).mp hzB, ?_⟩
    rw [mem_conjugate_iff] at hzy ⊢
    rw [show y * (q * z * q⁻¹) * y⁻¹ =
      (y * q * y⁻¹) * (y * z * y⁻¹) * (y * q * y⁻¹)⁻¹ by group]
    exact (mem_normalizer_iff.mp hyq _).mp hzy
  · apply B5a.mem_normalizer_of_map_le
    rintro _ ⟨q, hq, rfl⟩
    exact hy.conj_mem_Q hq

end Hyp52

end CFSG.ComponentClassification.GSThmB
