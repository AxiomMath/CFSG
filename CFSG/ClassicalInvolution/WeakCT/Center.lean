module

public import CFSG.ClassicalInvolution.WeakCT.Blocks

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat_apply_of_not_mem_left)
open scoped MatrixGroups

section Center

variable {K : Type} [Field K] {m k i : ℕ}

theorem eq_one_of_blockSL_mem_center (h : i + k ≤ m) (hk : k < m) {A : SL(k, K)}
    (hA : blockSL K m k i h A ∈ Subgroup.center SL(m, K)) : A = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  obtain ⟨a, ha⟩ : ∃ a : Fin m, ¬ (i ≤ a.val ∧ a.val < i + k) := by
    by_cases hi : i = 0
    · exact ⟨⟨k, hk⟩, by simp [hi]⟩
    · exact ⟨⟨0, by omega⟩, by simp; omega⟩
  have h1 := congrFun (congrFun (congrArg (fun g : Matrix (Fin m) (Fin m) K => g) hr) a) a
  rw [coe_blockSL, blockMat_apply_of_not_mem_left _ ha, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
  subst h1
  apply blockSL_injective h
  rw [map_one]
  exact Subtype.ext (by rw [← hr]; simp)

theorem center_inf_range_blockSL (h : i + k ≤ m) (hk : k < m) :
    Subgroup.center SL(m, K) ⊓ (blockSL K m k i h).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hz, A, rfl⟩
  rw [Subgroup.mem_bot, eq_one_of_blockSL_mem_center h hk hz, map_one]

variable {X : Type} [Group X]

theorem comp_blockSL_injective {θ : SL(m, K) →* X} (hθ : θ.ker ≤ Subgroup.center SL(m, K))
    (h : i + k ≤ m) (hk : k < m) : Function.Injective (θ.comp (blockSL K m k i h)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  exact eq_one_of_blockSL_mem_center h hk (hθ hA)

end Center

end CFSG.ClassicalInvolution.WeakCT
