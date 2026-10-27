module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf15Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW189b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

section OddCore



theorem trans_of_trans_at {Y : Type} [Group Y] {Λ : Set (Subgroup Y)} {K : Subgroup Y}
    (h : ∀ L ∈ Λ, ∃ y : Y, conjSub y K = L) : ∀ A ∈ Λ, ∀ B ∈ Λ, ∃ g : Y, conjSub g A = B := by
  intro A hA B hB
  obtain ⟨a, rfl⟩ := h A hA
  obtain ⟨b, rfl⟩ := h B hB
  exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩

theorem e189OddCoreQ8_proved : TwinThmEW.E189OddCoreQ8 := by
  intro n hih Y _ _ hlt Λ hS _ K hK htrans _ ⟨K', hK'tw, hK'ne⟩ z hz hodd
  exfalso
  obtain ⟨hK'Λ, w, hwK, hwK'⟩ := hK'tw
  have hzw : w = z := (hz.eq hwK).symm
  subst hzw
  have hedge : ∃ M ∈ Λ, ∃ N : Subgroup Y, N ∈ omegaNbr Λ M :=
    ⟨K, hK, K', Q3CL.T3.twin_mem_omegaNbr hS.hyp hK hK'Λ hK'ne hwK hwK'⟩
  exact hodd (TwinDisc.oddCentEdge_proved n hih.1 hih.2 Y hlt Λ hS (trans_of_trans_at htrans) hedge K hK w hwK)

end OddCore

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
