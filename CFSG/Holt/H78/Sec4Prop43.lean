module

public import CFSG.Holt.H78.Sec4Defs
import CFSG.Holt.H78.Sec4Prop43W
import CFSG.Holt.H78.Sec4Prop43R4
import CFSG.Holt.H78.Sec4LineDiag2

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.isEmpty_altConfig (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β) :
    IsEmpty (AltConfig G Ω α β) := by
  classical
  refine ⟨fun C => ?_⟩
  have hr : Fintype.card C.D.ι = 1 := by
    by_cases hT : Odd (Nat.card (twoPointKernel G Ω α β))
    · have h1 : 0 < Fintype.card C.D.ι := Fintype.card_pos_iff.mpr ⟨C.i₁⟩
      by_contra h
      exact C.false_of_odd_of_two_le hS hαβ hT (by omega)
    · exact C.card_ι_eq_one_of_ne_bot hS hαβ hT
  obtain ⟨W, hW, δ₁, δ₂, δ₃, h₁, h₂, h₃, h12, h13, h23, hF, hA5⟩ :=
    C.exists_W_of_card_ι_eq_one hS hαβ hr
  have hΔ' : holtDelta' G Ω α β = holtDelta G Ω α β :=
    C.holtDelta'_eq hS hαβ fun γ hγ => hS.holtDelta'_eq_orbit hαβ hγ
  have hs := hS.exists_smul_mem_holtDelta_of_fixSet hαβ hW h₁ h₂ h₃ h12 h13 h23 hF hA5
  have h5 := C.five_le_ncard_holtDelta hr
  have hAlt := alternatingGroup_le_inducedPerm_inf hαβ (C.alternatingGroup_le_twoPointSection hr)
  have hαΔ : α ∉ holtDelta G Ω α β := left_notMem_holtDelta hαβ
  have hβΔ : β ∉ holtDelta G Ω α β := right_notMem_holtDelta hαβ
  have hαΛ : α ∈ ({α, β} ∪ holtDelta G Ω α β : Set Ω) := Or.inl (Or.inl rfl)
  have h2tr := two_transitive_of_alternatingGroup_le (by omega) _ hAlt
  have hJ := isJClosed_union_holtDelta hS.star hαβ h2tr hΔ' hs
  have hclique := exists_mem_longInvAt_smul_eq_of_two_transitive hαβ h2tr hs
  have hβδ : ∀ δ ∈ holtDelta G Ω α β, ∃ s ∈ longInvAt G Ω α, s • β = δ := fun δ hδ => by
    rw [← hΔ'] at hδ
    exact hδ
  obtain ⟨w, hw⟩ := longInvSwap_nonempty hS.star α β
  obtain ⟨δw, hδw, -⟩ := hw.1.2
  have hwΛ : w ∈ stabilizer G ({α, β} ∪ holtDelta G Ω α β) :=
    hJ δw (Or.inr ⟨w, hw, hδw⟩) w ⟨hw.1, hδw⟩
  have hA := alternatingGroup_le_inducedPerm_union hαβ hαΔ hβΔ (by omega) _ hAlt
    (fun s hs => hJ α hαΛ s hs) ⟨w, hwΛ, hw.2⟩ hβδ hclique
  have h7 : 7 ≤ ({α, β} ∪ holtDelta G Ω α β : Set Ω).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_left.mpr fun y hy hyΔ => by
      rcases hy with rfl | rfl
      exacts [hαΔ hyΔ, hβΔ hyΔ]), Set.ncard_pair hαβ]
    omega
  have hND := hS.lineNonDiagonal_of_jClosed (Λ := {α, β} ∪ holtDelta G Ω α β) hαΛ h7 hJ
    (by convert hA)
  exact hS.false_of_altConfig_of_card_ι_eq_one hαβ C hr hΔ' hW h₁ h₂ h₃ h12 h13 h23 hF hA5 hND

end CFSG.Holt.H78
