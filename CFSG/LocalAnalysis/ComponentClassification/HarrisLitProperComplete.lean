module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitDihedralAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace ProperComplete

variable {N : Type} [Group N] [Finite N]

theorem subsingleton_of_isPerfect_of_comm {J : Type*} [Group J] (hJ : Group.IsPerfect J)
    (hc : ∀ x y : J, x * y = y * x) : Subsingleton J := by
  have hbot : commutator J = ⊥ := by
    rw [eq_bot_iff, commutator_def, commutator_le]
    intro x _ y _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm, hc]
  have htop := hJ.commutator_eq_top
  rw [hbot] at htop
  exact ⟨fun x y => by
    have hx : x ∈ (⊥ : Subgroup J) := htop ▸ mem_top x
    have hy : y ∈ (⊥ : Subgroup J) := htop ▸ mem_top y
    rw [mem_bot] at hx hy
    rw [hx, hy]⟩

end ProperComplete

end CFSG.ComponentClassification.HarrisLit
