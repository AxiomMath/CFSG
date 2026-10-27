module

public import CFSG.HardMathSupport.Foote.E27.SporSylow

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_sylow_kill (h : E27Config X K R T z) (hz : z ∈ K)
    (S₀ : Sylow 3 ↥K)
    (hkill : ∀ s : ↥K, s ∈ (S₀ : Subgroup ↥K) → orderOf s = 3 →
      81 ∣ Nat.card ↥((S₀ : Subgroup ↥K) ⊓ Subgroup.centralizer ({s} : Set ↥K)) ∨
        ∃ D : Subgroup ↥K, D ≤ Subgroup.centralizer ({s} : Set ↥K) ∧ ⁅D, D⁆ = D ∧
          3 ∣ Nat.card ↥D) :
    False := by
  obtain ⟨z₀, hz₀S₀, hord, hcard, hperf, -⟩ := h.exists_conj_mem_sylow hz S₀
  rcases hkill z₀ hz₀S₀ hord with h81 | ⟨D, hD, hDp, hdvd⟩
  · rw [hcard] at h81
    norm_num at h81
  · exact hperf D hD hDp hdvd

end CFSG.HardMathSupport.Foote.E27

end
