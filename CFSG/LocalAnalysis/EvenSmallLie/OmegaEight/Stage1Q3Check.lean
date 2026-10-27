module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelCheck
public import Certificates.Certificate3375

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native


noncomputable def flagOrbitW : Array (Array ℕ) := Classical.choose Certificates.certificate3375

theorem q3Check_true : q3CheckW flagOrbitW = true :=
  Classical.choose_spec Certificates.certificate3375

theorem q3_parts :
    (∀ k < 6, (uArr .plus k)[0]! = 0) ∧
    eqA 120 (oOrbitW .plus)[0]! (idA 120) = true ∧
    (∀ i < (oOrbitW .plus).size, (∀ s ∈ uOrig .plus, stabB s oMasksW[i]! = true) → i = 0) ∧
    flagOrbitW.size = 315 ∧ eqA 120 flagOrbitW[0]! (idA 120) = true ∧
    (∀ j < flagOrbitW.size, isInvA 120 flagOrbitW[j]! (invCand 120 flagOrbitW[j]!) = true ∧
      memP .plus flagOrbitW[j]! = true) ∧
    (∀ j < flagOrbitW.size, ∀ j' < j, ∃ z < 120,
      ((fMasksAW flagOrbitW)[j]!).getD z false ≠ ((fMasksAW flagOrbitW)[j']!).getD z false ∨
        ((fMasksBW flagOrbitW)[j]!).getD z false ≠ ((fMasksBW flagOrbitW)[j']!).getD z false) ∧
    (∀ s ∈ uOrig .plus, stabB s flagA = true ∧ stabB s flagB = true) ∧
    (∀ j < flagOrbitW.size,
      (∀ s ∈ uOrig .plus, stabB s (fMasksAW flagOrbitW)[j]! = true ∧
        stabB s (fMasksBW flagOrbitW)[j]! = true) → j = 0) ∧
    isInvA 360 rho2Arr (invCand 360 rho2Arr) = true ∧
    (∀ k < 6, eqA 120 (OmegaEight.copy0Arr (utArr k)) (uArr .plus k) = true ∧
      memU .plus (sigArr (utArr k)) = true) ∧
    (∀ j < 6, eqA 120 (sigArr (psiTT .plus (2 ^ j))) (sigTarget j) = true) := by
  have h := q3Check_true
  have hr := r3CheckW_oOrbitW
  simp only [q3CheckW, Bool.and_eq_true, allLt_iff, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true', Array.all_eq_true, List.any_eq_true, List.mem_range, bne_iff_ne,
    ne_eq] at h
  simp only [r3CheckW, Bool.and_eq_true, allLt_iff, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  obtain ⟨h2, h3⟩ := hr
  refine ⟨h1, h2, fun i hi hs => ?_, h4, h5, h6, h7, fun s hs => ?_, fun j hj hs => ?_, h10, h11,
    h12⟩
  · rcases h3 i hi with h | h
    · exfalso
      have : ((uOrig .plus).all fun s => stabB s (maskOf .plus (oOrbitW .plus)[i]!)) = true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro s hs'
        have e : oMasksW[i]! = maskOf .plus (oOrbitW .plus)[i]! := by
          rw [oMasksW, getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos _ i hi]
        rw [← e]
        exact hs s hs'
      rw [h] at this
      exact absurd this (by decide)
    · exact h
  · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hs
    exact h8 k hk
  · rcases h9 j hj with h | h
    · exfalso
      have : ((uOrig .plus).all fun s => stabB s (fMasksAW flagOrbitW)[j]! &&
          stabB s (fMasksBW flagOrbitW)[j]!) = true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro s hs'
        rw [Bool.and_eq_true]
        exact hs s hs'
      rw [h] at this
      exact absurd this (by decide)
    · exact h

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model
