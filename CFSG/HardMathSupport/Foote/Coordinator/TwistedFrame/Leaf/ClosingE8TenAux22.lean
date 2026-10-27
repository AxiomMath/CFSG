module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData5
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux14

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

set_option linter.unusedSectionVars false


section Fin

variable {L : Type} [Field L]

@[expose] def Tm (c d z : L) : Fn L →ₗ[L] Fn L :=
  actOp aE8 vA6 c ∘ₗ actOp aE8 vA7 d ∘ₗ actOp aE8 vGc z

theorem actOp_eval (g : Fin Tag.E8.rank → ℤ) (t : L) (f : Fn L) (ξ : Fin Tag.E8.rank → ℤ) :
    actOp aE8 g t f ξ = f ξ + t * (aE8 g (ξ - g) : L) * f (ξ - g) := by
  rw [actOp_apply]
  rfl

theorem T_extract_a (c d z : L) (u : Fn L) (ν : Fin Tag.E8.rank → ℤ)
    (h0 : u (ν + vA6) = 0) (h1 : u (ν + vA6 - vGc) = 0) (h2 : u (ν + vA6 - vA7) = 0)
    (h3 : u (ν + vA6 - vA7 - vGc) = 0) (h5 : u (ν - vGc) = 0) (h6 : u (ν - vA7) = 0)
    (h7 : u (ν - vA7 - vGc) = 0) :
    Tm c d z u (ν + vA6) = c * (aE8 vA6 ν : L) * u ν := by
  simp only [Tm, LinearMap.comp_apply, actOp_eval, add_sub_cancel_right]
  rw [h0, h1, h2, h3, h5, h6, h7]
  ring

theorem T_extract_b (c d z : L) (u : Fn L) (ν : Fin Tag.E8.rank → ℤ)
    (h0 : u (ν + vA7) = 0) (h1 : u (ν + vA7 - vGc) = 0) (h3 : u (ν - vGc) = 0)
    (h4 : u (ν + vA7 - vA6) = 0) (h5 : u (ν + vA7 - vA6 - vGc) = 0)
    (h6 : u (ν + vA7 - vA6 - vA7) = 0) (h7 : u (ν + vA7 - vA6 - vA7 - vGc) = 0) :
    Tm c d z u (ν + vA7) = d * (aE8 vA7 ν : L) * u ν := by
  simp only [Tm, LinearMap.comp_apply, actOp_eval, add_sub_cancel_right]
  rw [h0, h1, h3, h4, h5, h6, h7]
  ring

theorem vA6_data : vA6 ∈ rootFinset Tag.E8 ∧ vA6 7 = 0 := by
  unfold vA6
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem vA7_data : vA7 ∈ rootFinset Tag.E8 ∧ vA7 7 = 0 := by
  unfold vA7
  simp only [rootFinset_E8_eq]
  decide +kernel

theorem Y1_vanish {c d z : L} (hc : c ≠ 0) (hd : d ≠ 0) (u : Fn L)
    (hsupp : ∀ ν, u ν ≠ 0 → ν ∈ mRoots)
    (h₁ : ∀ ν ∈ mRoots, ν + vGp ∈ rootFinset Tag.E8 → u ν = 0)
    (h₂ : ∀ ν ∈ mRoots, ν + vGc ∈ rootFinset Tag.E8 → u ν = 0)
    (h₃ : ∀ μ ∈ mRoots, μ + vGp ∈ rootFinset Tag.E8 → Tm c d z u μ = 0) :
    ∀ ν ∈ mRoots, (cls ν = 2 ∨ cls ν = 3) → u ν = 0 := by
  have hu0 : ∀ ξ, Vz ξ → u ξ = 0 := by
    intro ξ hξ
    rcases hξ with h | h | h
    · by_contra hne
      exact h (hsupp ξ hne)
    · by_cases hm : ξ ∈ mRoots
      · exact h₁ ξ hm h
      · by_contra hne
        exact hm (hsupp ξ hne)
    · by_cases hm : ξ ∈ mRoots
      · exact h₂ ξ hm h
      · by_contra hne
        exact hm (hsupp ξ hne)
  intro ν hν hcls
  by_cases hp : ν + vGp ∈ rootFinset Tag.E8
  · exact h₁ ν hν hp
  by_cases hq : ν + vGc ∈ rootFinset Tag.E8
  · exact h₂ ν hν hq
  have hνd : ν ∈ deg1Roots :=
    mem_deg1Roots.2 ⟨(mem_mRoots.1 hν).1, (mem_mRoots.1 hν).2.1⟩
  rcases S0_cases ν hν hcls hp hq with
    ⟨hμ, hμp, c0, c1, c2, c3, c5, c6, c7⟩ | ⟨hμ, hμp, c0, c1, c3, c4, c5, c6, c7⟩
  · have hT := h₃ (ν + vA6) hμ hμp
    rw [T_extract_a c d z u ν (hu0 _ c0) (hu0 _ c1) (hu0 _ c2) (hu0 _ c3) (hu0 _ c5) (hu0 _ c6)
      (hu0 _ c7)] at hT
    have hA : (aE8 vA6 ν : L) ≠ 0 :=
      aE8_cast_ne_zero vA6_data.1 vA6_data.2 hνd (by
        rw [add_comm]
        exact (mem_mRoots.1 hμ).1 |> mem_rootFinset.2)
    exact (mul_eq_zero.1 hT).resolve_left (mul_ne_zero hc hA)
  · have hT := h₃ (ν + vA7) hμ hμp
    rw [T_extract_b c d z u ν (hu0 _ c0) (hu0 _ c1) (hu0 _ c3) (hu0 _ c4) (hu0 _ c5) (hu0 _ c6)
      (hu0 _ c7)] at hT
    have hA : (aE8 vA7 ν : L) ≠ 0 :=
      aE8_cast_ne_zero vA7_data.1 vA7_data.2 hνd (by
        rw [add_comm]
        exact (mem_mRoots.1 hμ).1 |> mem_rootFinset.2)
    exact (mul_eq_zero.1 hT).resolve_left (mul_ne_zero hd hA)

end Fin

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
