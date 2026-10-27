module

public import CFSG.ClassicalInvolution.Asc77.AscC25W8
public import CFSG.ClassicalInvolution.Asc77.AscC25W9

public section

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace CFSG.ClassicalInvolution.Asc77.C25W.Sp

variable {F : Type} [Field F]

theorem scalar_of_proj_eq_one {x : StatedSp 2 F} (h : proj 2 F x = 1) :
    ∃ c : F, mat 2 F x = c • 1 := by
  have hx : x ∈ spScalars 2 F := by rw [← ker_proj]; exact h
  have hx' : (x : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedScalars (Fin 2 ⊕ Fin 2) F := hx
  rw [StatedScalars, MonoidHom.mem_range] at hx'
  obtain ⟨c, hc⟩ := hx'
  refine ⟨c, ?_⟩
  rw [mat_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem orderOf_proj_eq_four {s : StatedSp 2 F} (hs4 : s * s * (s * s) = 1)
    (hsc : ¬ ∃ c : F, mat 2 F (s * s) = c • 1) : orderOf (proj 2 F s) = 4 := by
  have h4 : proj 2 F s ^ (2 ^ (1 + 1)) = 1 := by
    rw [← map_pow]
    have : s ^ (2 ^ (1 + 1)) = s * s * (s * s) := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, pow_two]
    rw [this, hs4, map_one]
  have h2 : ¬ proj 2 F s ^ (2 ^ 1) = 1 := by
    intro h
    rw [← map_pow] at h
    have : s ^ (2 ^ 1) = s * s := by rw [pow_one, pow_two]
    rw [this] at h
    exact hsc (scalar_of_proj_eq_one h)
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
  simpa using this

theorem psp4_sq_fixed [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (β : MulAut (StatedProj (StatedSp 2 F))) (hβ : β * β * (β * β) = 1) :
    ∃ (u w : Fin 2 ⊕ Fin 2 → F) (s : StatedSp 2 F), form u w = 1 ∧
      s ∈ planeGroup (Submodule.span F {u, w}) ∧ orderOf (proj 2 F s) = 4 ∧
      β (β (proj 2 F s)) = proj 2 F s := by
  obtain ⟨Nl, τ, l, c', N₁, hττ, hl, hNl, hN₁, hc'1, hN₁τ, hsq⟩ := normal_form_sq h2 h4 β hβ
  obtain ⟨u, w, s, huw, hs, hs4, hsc, hcomm⟩ :=
    exists_stable_rotation (m := 0) τ N₁ hττ h2 hN₁ c' hc'1 hN₁τ
  refine ⟨u, w, s, huw, hs, orderOf_proj_eq_four hs4 hsc, ?_⟩
  have e1 : β (β (proj 2 F s)) = (β * β) (proj 2 F s) := rfl
  rw [e1, hsq, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_fieldSp, hNl]
  have e := hcomm
  rw [mat_apply] at e
  rw [Matrix.smul_mul, e, Matrix.mul_smul]

end CFSG.ClassicalInvolution.Asc77.C25W.Sp
