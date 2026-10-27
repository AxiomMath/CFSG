module

public import CFSG.LinearAlgebra.LinearGroups.Elations
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LinearGroups

variable {K : Type*} [Field K]

theorem coe_scalarSubgroup_two :
    ((scalarSubgroup 2 K : Subgroup (SpecialLinearGroup (Fin 2) K)) :
      Set (SpecialLinearGroup (Fin 2) K)) = {1, -1} := by
  ext A
  rw [SetLike.mem_coe, mem_scalarSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl, hA⟩
    have hl' : ((l : K) - 1) * ((l : K) + 1) = 0 := by
      have := congrArg Units.val hl
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      linear_combination this
    rcases mul_eq_zero.1 hl' with h | h
    · left
      refine Subtype.ext ?_
      rw [hA, sub_eq_zero.1 h]
      simp
    · right
      refine Subtype.ext ?_
      rw [hA, eq_neg_of_add_eq_zero_left h]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Matrix.one_apply_ne hij]
  · rintro (rfl | rfl)
    · exact ⟨1, one_pow 2, by simp⟩
    · refine ⟨-1, by rw [neg_one_sq], ?_⟩
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Matrix.one_apply_ne hij]

end CFSG.QuasithinUnique
