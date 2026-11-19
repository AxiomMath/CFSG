module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec4M_perm_trichotomy {α : Type} [DecidableEq α] (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    σ = 1 ∨ (∃ a b : α, a ≠ b ∧ σ = Equiv.swap a b) ∨
      ∃ x y : α, σ x ≠ x ∧ σ y ≠ y ∧ y ≠ x ∧ y ≠ σ x := by
  classical
  have hσσ : ∀ y : α, σ (σ y) = y := by
    intro y
    have h := congrArg (fun e : Equiv.Perm α => e y) hσ
    simpa [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
  by_cases hfix : ∀ x : α, σ x = x
  · left
    ext x
    exact hfix x
  · right
    push Not at hfix
    obtain ⟨x, hx⟩ := hfix
    by_cases hmove : ∀ y : α, σ y ≠ y → y = x ∨ y = σ x
    · left
      refine ⟨x, σ x, fun h => hx h.symm, ?_⟩
      ext y
      by_cases hy : σ y = y
      · have hyx : y ≠ x := fun h => hx (h ▸ hy)
        have hyσx : y ≠ σ x := by
          intro h
          apply hx
          have h' := hy
          rw [h, hσσ x] at h'
          exact h'.symm
        rw [hy, Equiv.swap_apply_of_ne_of_ne hyx hyσx]
      · rcases hmove y hy with h | h
        · rw [h, Equiv.swap_apply_left]
        · rw [h, hσσ x, Equiv.swap_apply_right]
    · right
      push Not at hmove
      obtain ⟨y, hy, hyx, hyσx⟩ := hmove
      exact ⟨x, y, hx, hy, hyx, hyσx⟩

end CFSG.OddStandard.SmallF3.Omega
