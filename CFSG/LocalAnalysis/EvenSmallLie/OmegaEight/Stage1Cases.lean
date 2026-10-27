module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1E
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1S5

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
include hS

theorem Zset_cases [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    (∀ v, v ∈ Zset t Q ψ) ∨ (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) := by
  obtain ⟨v₀, hv₀Z, hv₀⟩ := hS.exists_ne_zero_mem_Zset hG hnab
  have hne : ∀ u : V6, qfV ε u = 1 → u ≠ 0 := fun u hu h => by
    rw [h, qfV_zero] at hu; exact zero_ne_one hu
  by_cases hN : ∃ w ∈ Zset t Q ψ, qfV ε w = 1
  · obtain ⟨w, hwZ, hw⟩ := hN
    have hallN : ∀ u, qfV ε u = 1 → u ∈ Zset t Q ψ := fun u hu =>
      hS.mem_Zset_of (hne w hw) (hne u hu) (hw.trans hu.symm) hwZ
    by_cases hSg : ∃ s ∈ Zset t Q ψ, s ≠ 0 ∧ qfV ε s = 0
    · obtain ⟨s, hsZ, hs0, hs⟩ := hSg
      left
      intro v
      by_cases hv : v = 0
      · exact hv ▸ hS.zero_mem_Zset
      · rcases qfV_cases ε v with h | h
        · exact hS.mem_Zset_of hs0 hv (hs.trans h.symm) hsZ
        · exact hallN v h
    · exfalso
      refine hS.false_of_Zset_eq fun v => ⟨fun hv => ?_, fun hv => ?_⟩
      · by_cases h0 : v = 0
        · exact Or.inl h0
        · rcases qfV_cases ε v with h | h
          · exact absurd ⟨v, hv, h0, h⟩ hSg
          · exact Or.inr h
      · rcases hv with rfl | h
        · exact hS.zero_mem_Zset
        · exact hallN v h
  · right
    have hv₀s : qfV ε v₀ = 0 := (qfV_cases ε v₀).resolve_right fun h => hN ⟨v₀, hv₀Z, h⟩
    intro v
    constructor
    · intro hv
      exact (qfV_cases ε v).resolve_right fun h => hN ⟨v, hv, h⟩
    · intro hv
      by_cases h0 : v = 0
      · exact h0 ▸ hS.zero_mem_Zset
      · exact hS.mem_Zset_of hv₀ h0 (hv₀s.trans hv.symm) hv₀Z

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
