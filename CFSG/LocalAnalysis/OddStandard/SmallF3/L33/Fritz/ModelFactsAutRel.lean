module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutElems

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

namespace IsL33Model

variable {L : Type} [Group L] {M : AutModel L (Equiv.Perm (Fin 26))}
  (h : IsL33Model M)

theorem elX_pow_eight : h.elX ^ 8 = 1 := by
  apply M.e.injective
  apply Subtype.ext
  simp only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, h.e_elX]
  exact model_relations.1

theorem elX_pow_four_ne_one : h.elX ^ 4 ≠ 1 := by
  intro h1
  refine model_relations.2.1 ?_
  have h2 := congrArg (fun g : L => (M.e g : Equiv.Perm (Fin 26))) h1
  simpa only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, h.e_elX] using h2

theorem elY_sq : h.elY ^ 2 = 1 := by
  apply M.e.injective
  apply Subtype.ext
  simp only [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, h.e_elY]
  exact model_relations.2.2.1

theorem elY_conj : h.elY * h.elX * h.elY⁻¹ = h.elX ^ 3 := by
  apply M.e.injective
  apply Subtype.ext
  simp only [map_mul, map_inv, map_pow, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
    h.e_elX, h.e_elY]
  exact model_relations.2.2.2.2.1

theorem elK_sq : h.elK ^ 2 = 1 := by
  apply M.ι_injective
  rw [map_pow, map_one, h.ι_elK]
  exact model_relations.2.2.2.1

theorem elK_outer : ¬ ∃ a : L, ∀ u : L, h.elK u = a * u * a⁻¹ := by
  rintro ⟨a, ha⟩
  exact h.modelK_not_mem_P
    ((liftA_inner_iff M h.P_le_A h.modelK_mem_A).1 ⟨a, fun u => ha u⟩)

theorem elK_x : h.elK h.elX = h.elX * h.elX ^ 4 := by
  rw [apply_eq_iff (M := M)]
  simp only [h.ι_elK, map_mul, map_pow, h.e_elX, Subgroup.coe_mul, Subgroup.coe_pow]
  exact model_relations.2.2.2.2.2.1

theorem elK_y : h.elK h.elY = h.elY := by
  rw [apply_eq_iff (M := M), h.ι_elK, h.e_elY]
  have hc := model_relations.2.2.2.2.2.2.1
  rw [← hc]
  group

theorem elD_sq : (MulAut.conj (h.elX * h.elY) * h.elK) ^ 2 = 1 := by
  apply M.ι_injective
  simp only [map_pow, map_mul, map_one, h.ι_conj, h.ι_elK, h.e_elX, h.e_elY,
    Subgroup.coe_mul]
  exact model_relations.2.2.2.2.2.2.2

theorem elD_outer : ¬ ∃ a : L, ∀ u : L, (MulAut.conj (h.elX * h.elY) * h.elK) u = a * u * a⁻¹ := by
  rintro ⟨a, ha⟩
  refine h.elK_outer ⟨(h.elX * h.elY)⁻¹ * a, fun u => ?_⟩
  have h1 := ha u
  rw [MulAut.mul_apply, MulAut.conj_apply] at h1
  have h2 : h.elK u = (h.elX * h.elY)⁻¹ * (a * u * a⁻¹) * (h.elX * h.elY) := by
    rw [← h1]
    group
  rw [h2]
  group

theorem elG1_pow : h.elG1 ^ 3 = 1 := by
  apply M.ι_injective
  rw [map_pow, map_one, h.ι_elG1]
  exact model_three_one.1

theorem elG1_z : h.elG1 (h.elX ^ 4) = h.elY := by
  rw [apply_eq_iff (M := M)]
  simp only [h.ι_elG1, map_pow, h.e_elX, h.e_elY, Subgroup.coe_pow]
  simpa only [modelZ] using model_three_one.2.1

theorem elG1_y : h.elG1 h.elY = h.elX ^ 4 * h.elY := by
  rw [apply_eq_iff (M := M)]
  simp only [h.ι_elG1, h.e_elY, map_mul, map_pow, h.e_elX, Subgroup.coe_mul,
    Subgroup.coe_pow]
  simpa only [modelZ] using model_three_one.2.2.1

theorem elG1_k : h.elG1 * h.elK * h.elG1⁻¹ = h.elK := by
  apply M.ι_injective
  rw [map_mul, map_mul, map_inv, h.ι_elG1, h.ι_elK]
  exact model_three_one.2.2.2

theorem elG2_pow : h.elG2 ^ 3 = 1 := by
  apply M.ι_injective
  rw [map_pow, map_one, h.ι_elG2]
  exact model_three_two.1

theorem elG2_z : h.elG2 (h.elX ^ 4) = h.elX ^ 2 * h.elY := by
  rw [apply_eq_iff (M := M)]
  simp only [h.ι_elG2, map_pow, h.e_elX, map_mul, h.e_elY, Subgroup.coe_pow,
    Subgroup.coe_mul]
  simpa only [modelZ] using model_three_two.2.1

theorem elG2_w : h.elG2 (h.elX ^ 2 * h.elY) = h.elX ^ 4 * (h.elX ^ 2 * h.elY) := by
  rw [apply_eq_iff (M := M)]
  simp only [h.ι_elG2, map_mul, map_pow, h.e_elX, h.e_elY, Subgroup.coe_mul,
    Subgroup.coe_pow]
  simpa only [modelZ] using model_three_two.2.2.1

theorem elG2_zk : h.elG2 * (MulAut.conj (h.elX ^ 4) * h.elK) * h.elG2⁻¹ =
    MulAut.conj (h.elX ^ 4) * h.elK := by
  apply M.ι_injective
  simp only [map_mul, map_inv, h.ι_conj, h.ι_elG2, h.ι_elK, map_pow, h.e_elX,
    Subgroup.coe_pow]
  simpa only [modelZ] using model_three_two.2.2.2

end IsL33Model

end CFSG.OddStandard.SmallF3.L33
