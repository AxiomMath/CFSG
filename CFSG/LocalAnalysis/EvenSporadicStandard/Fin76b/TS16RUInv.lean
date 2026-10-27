module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCos
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.Sporadic.SmallOddCore

section


theorem repCoset_five : ∀ j < 9, repCoset[j]! = 5 → j = 5 := by decide

theorem repCoset_seven : ∀ j < 9, repCoset[j]! = 7 → j = 4 := by decide

theorem inv_coset_class {k : ℕ} (hk : k = 5 ∨ k = 7) {β : Equiv.Perm (Fin 820)}
    (hβ : β ∈ U43ExtStar) (h2 : β * β = 1) (hc : InCos k β) :
    ∃ c ∈ P, β = c * rP (if k = 5 then 5 else 4) * c⁻¹ := by
  have hk8 : k < 8 := by rcases hk with rfl | rfl <;> norm_num
  have hβ1 : β ≠ 1 := by
    intro h
    have h1 : tP k ∈ P := by
      have := hc
      rw [h] at this
      unfold InCos at this
      simpa using this
    have := (tP_mem_P_iff hk8).1 h1
    rcases hk with rfl | rfl <;> omega
  obtain ⟨j, hj, ⟨c, hcP, hβc⟩, g, hg, hβg⟩ := involution_data (U43ExtStar_le_R hβ) h2 hβ1
  have hjk : repCoset[j]! = k :=
    inCos_unique (repCoset_lt hj) hk8 (inCos_iff.2 ⟨g, hg, hβg⟩) hc
  rcases hk with rfl | rfl
  · have := repCoset_five j hj hjk
    subst this
    exact ⟨c, hcP, by simpa using hβc⟩
  · have := repCoset_seven j hj hjk
    subst this
    exact ⟨c, hcP, by simpa using hβc⟩

theorem inv_coset_conj {k : ℕ} (hk : k = 5 ∨ k = 7) {β β' : Equiv.Perm (Fin 820)}
    (hβ : β ∈ U43ExtStar) (hβ' : β' ∈ U43ExtStar) (h2 : β * β = 1) (h2' : β' * β' = 1)
    (hc : InCos k β) (hc' : InCos k β') : ∃ c ∈ P, β' = c * β * c⁻¹ := by
  obtain ⟨c₁, hc₁, h₁⟩ := inv_coset_class hk hβ h2 hc
  obtain ⟨c₂, hc₂, h₂⟩ := inv_coset_class hk hβ' h2' hc'
  refine ⟨c₂ * c₁⁻¹, P.mul_mem hc₂ (P.inv_mem hc₁), ?_⟩
  rw [h₁, h₂]
  group

end

end CFSG.EvenSporadicStandard.Fin76b.U16
