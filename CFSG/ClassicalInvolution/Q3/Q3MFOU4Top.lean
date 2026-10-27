module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem isPGroup_center_su4 : IsPGroup 2 (Subgroup.center (Su F9 3 1 4)) := by
  intro z
  refine ⟨2, ?_⟩
  obtain ⟨u, -, hu⟩ := scalar_of_mem_center z.2
  have h4 : u ^ 4 = 1 := by
    have h1 := det_suMat (z : Su F9 3 1 4)
    rw [hu, Matrix.det_smul, Matrix.det_one] at h1
    simpa using h1
  apply Subtype.ext
  apply suMat_injective
  show suMat ((z : Su F9 3 1 4) ^ 2 ^ 2) = suMat 1
  rw [suMat_pow, hu, suMat_one, smul_pow, one_pow, show (2 : ℕ) ^ 2 = 4 from rfl, h4, one_smul]

theorem oddCoreIn_fixed_eq_bot_su4 (hq : CFSG.Open.IsQuasisimple (Su F9 3 1 4))
    (hZ : IsPGroup 2 (Subgroup.center (Su F9 3 1 4)))
    (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F3))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F3)))
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4))) (hρ2 : ρ * ρ = 1)
    (g₀ : Su F9 3 1 4)
    (hfix : ∀ r ∈ (rootSU2 F9 3 1 (by norm_num : 2 ≤ 4)).map (MulAut.conj g₀).toMonoidHom,
      ρ (QuotientGroup.mk r) = QuotientGroup.mk r) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  obtain ⟨c, hc⟩ : ∃ c : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)),
      c = MulAut.conj (QuotientGroup.mk g₀ : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) :=
    ⟨_, rfl⟩
  obtain ⟨ρ'', hρ''⟩ : ∃ ρ'' : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)),
      ρ'' = c⁻¹ * ρ * c := ⟨_, rfl⟩
  have hcr : ∀ r : Su F9 3 1 4, c (QuotientGroup.mk r) = QuotientGroup.mk (g₀ * r * g₀⁻¹) := by
    intro r
    rw [hc]
    rfl
  have hρ''fix : ∀ r ∈ rootSU2 F9 3 1 (by norm_num : 2 ≤ 4),
      ρ'' (QuotientGroup.mk r) = QuotientGroup.mk r := by
    intro r hr
    have h1 : ρ (c (QuotientGroup.mk r)) = c (QuotientGroup.mk r) := by
      rw [hcr]
      exact hfix _ ⟨r, hr, rfl⟩
    rw [hρ'']
    show c⁻¹ (ρ (c (QuotientGroup.mk r))) = QuotientGroup.mk r
    rw [h1]
    exact MulAut.inv_apply_self _ c _
  have hρ''2 : ρ'' * ρ'' = 1 := by
    calc ρ'' * ρ'' = c⁻¹ * (ρ * ρ) * c := by rw [hρ'']; group
      _ = 1 := by rw [hρ2]; group
  have h1 := su4_core hq hZ hSp hSpZ ρ'' hρ''2 hρ''fix
  have h2 := oddCoreIn_fixed_conj_eq_bot c ρ'' h1
  have hρρ'' : c * ρ'' * c⁻¹ = ρ := by
    rw [hρ'']
    group
  rwa [hρρ''] at h2

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
