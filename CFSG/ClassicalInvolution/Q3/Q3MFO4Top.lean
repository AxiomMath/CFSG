module

public import CFSG.ClassicalInvolution.Q3.Q3MFO4Fix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFO4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4 CFSG.ClassicalInvolution.Asc77.CX.MF2L
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Top

variable {F : Type} [Field F] [Finite F]

theorem oddCoreIn_fixed_eq_bot_sl4 (hF : Nat.card F = 3)
    (hSL : CFSG.Open.IsQuasisimple SL(4, F)) (hSLZ : IsPGroup 2 (Subgroup.center SL(4, F)))
    (hSp : CFSG.Open.IsQuasisimple (StatedSp 2 F))
    (hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F)))
    (ρ : MulAut (SL(4, F) ⧸ Subgroup.center SL(4, F))) (hρ2 : ρ * ρ = 1) (g₀ : SL(4, F))
    (hfix : ∀ r ∈ (rootSL2 F (by norm_num : 2 ≤ 4)).map (MulAut.conj g₀).toMonoidHom,
      ρ (QuotientGroup.mk r) = QuotientGroup.mk r) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  obtain ⟨c, hc⟩ : ∃ c : MulAut (SL(4, F) ⧸ Subgroup.center SL(4, F)),
      c = MulAut.conj (QuotientGroup.mk g₀ : SL(4, F) ⧸ Subgroup.center SL(4, F)) := ⟨_, rfl⟩
  obtain ⟨ρ'', hρ''⟩ : ∃ ρ'' : MulAut (SL(4, F) ⧸ Subgroup.center SL(4, F)),
      ρ'' = c⁻¹ * ρ * c := ⟨_, rfl⟩
  have hcr : ∀ r : SL(4, F), c (QuotientGroup.mk r) = QuotientGroup.mk (g₀ * r * g₀⁻¹) := by
    intro r
    rw [hc]
    rfl
  have hρ''fix : ∀ r ∈ rootSL2 F (by norm_num : 2 ≤ 4),
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
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : MulAut (projectiveSL 4 F),
      ρ' = (MulAut.congr (projEquiv (F := F))).symm ρ'' := ⟨_, rfl⟩
  have hρρ' : MulAut.congr (projEquiv (F := F)) ρ' = ρ'' := by
    rw [hρ']
    exact (MulAut.congr (projEquiv (F := F))).apply_symm_apply ρ''
  have hρe : ∀ x, (projEquiv (F := F)) (ρ' x) = ρ'' ((projEquiv (F := F)) x) := by
    intro x
    have := congrArg (fun φ : MulAut (SL(4, F) ⧸ Subgroup.center SL(4, F)) =>
      φ ((projEquiv (F := F)) x)) hρρ'
    simpa [MulAut.congr_apply] using this
  have hρ'2 : ρ' * ρ' = 1 := by
    rw [hρ', ← map_mul, hρ''2, map_one]
  have hρ'fix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
      ρ' (proj 4 F r) = proj 4 F r := by
    intro r hr
    apply (projEquiv (F := F)).injective
    have h2 : (projEquiv (F := F)) (proj 4 F r) = QuotientGroup.mk r := rfl
    rw [hρe, h2]
    exact hρ''fix r hr
  have hcore := oddCoreIn_fixed_eq_bot_proj4 hF hSL hSLZ hSp hSpZ ρ' hρ'2 hρ'fix
  have h1 := oddCoreIn_fixed_congr_eq_bot' (projEquiv (F := F)) ρ' hcore
  rw [hρρ'] at h1
  have h2 := oddCoreIn_fixed_conj_eq_bot c ρ'' h1
  have hρρ'' : c * ρ'' * c⁻¹ = ρ := by
    rw [hρ'']
    group
  rwa [hρρ''] at h2

end Top

end CFSG.ClassicalInvolution.Q3.Q3MFO4
