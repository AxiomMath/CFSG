module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public section

namespace CFSG.GorensteinWalter

universe u

variable {K : Type u} [Field K]

theorem pgl2_sq_mem_psl2Range (g : Matrix.ProjGenLinGroup (Fin 2) K) :
    g ^ 2 ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [← map_pow, pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_pow_eq_pow_val, Matrix.det_pow]
  exact ⟨_, sq _⟩

theorem pgl2_mem_psl2Range_of_pow_odd {g : Matrix.ProjGenLinGroup (Fin 2) K} {n : ℕ} (hn : Odd n)
    (hg : g ^ n = 1) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  obtain ⟨k, rfl⟩ := hn
  have h : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hg, one_mul]
  rw [h]
  exact Subgroup.pow_mem _ (pgl2_sq_mem_psl2Range g) _

theorem pgl2_mem_psl2Range_of_odd_orderOf {g : Matrix.ProjGenLinGroup (Fin 2) K}
    (hg : Odd (orderOf g)) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  pgl2_mem_psl2Range_of_pow_odd hg (pow_orderOf_eq_one g)

end CFSG.GorensteinWalter
