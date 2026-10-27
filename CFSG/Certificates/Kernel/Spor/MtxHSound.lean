module

public import Certificates.Data.Kernel.Spor.MtxH
public import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Certificates.Kernel.MtxKSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.MtxH

open CFSG.KS.Raw CFSG.Sporadic.SuzOddCore CFSG.KC.Mtx

theorem tokHOK_lt {w P h₀ h₁ h₂ h₃ k v : Nat} (hk : k < 4)
    (h : tokHOK w P h₀ h₁ h₂ h₃ k v = true) : v = [h₀, h₁, h₂, h₃].getD k 0 := by
  interval_cases k <;> exact Nat.eq_of_beq_eq_true h

theorem mtxHK_sound {n w P h₀ h₁ h₂ h₃ : Nat} {cs : List Char}
    (h : mtxHK n w P h₀ h₁ h₂ h₃ cs = true) :
    mtxHeader (String.ofList cs) = [h₀, h₁, h₂, h₃] ∧
      (mtxImages (String.ofList cs)).length = n ∧
      mtxArr (String.ofList cs) = unpack n w P := by
  obtain ⟨hl, ht⟩ := runT_sound (tok := tokHOK w P h₀ h₁ h₂ h₃) h
  refine ⟨?_, by simp [mtxImages, hl], mtxArr_of_tokens hl fun i hi => ?_⟩
  · apply List.ext_getElem
    · simp [mtxHeader, hl]
    · intro i h1 h2
      have hi : i < 4 := by simpa using h2
      have := tokHOK_lt hi (ht i (by omega))
      rw [getD_of_lt _ (by omega)] at this
      simp only [mtxHeader, List.getElem_map, List.getElem_take]
      rw [this, getD_of_lt _ h2]
  · have := ht (4 + i) (by omega)
    unfold tokHOK at this
    have h4 : Nat.blt (4 + i) 4 = false := by
      cases e : Nat.blt (4 + i) 4
      · rfl
      · have := Nat.blt_eq.mp e
        omega
    rw [h4] at this
    have e := field_of_tok this
    rwa [Nat.add_sub_cancel_left] at e

end CFSG.KC.MtxH

end
