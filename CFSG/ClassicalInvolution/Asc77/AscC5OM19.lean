module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM12

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem scalar_mem_gsp (c : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ gsp 2 F := by
  refine mem_gsp.mpr ⟨c * c, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mul,
    ← Matrix.smul_one_eq_diagonal]
  simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul]

@[expose] noncomputable def smulGsp (c : Fˣ) (M : gsp 2 F) : gsp 2 F :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c * M, (gsp 2 F).mul_mem (scalar_mem_gsp c)
    M.2⟩

theorem gm_smulGsp (c : Fˣ) (M : gsp 2 F) : gm (smulGsp c M) = (c : F) • gm M := by
  change ((Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : GL _ F) : Matrix _ _ F) * gm M = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mul, Matrix.one_mul]

theorem mu_smulGsp (c : Fˣ) (M : gsp 2 F) : mu (smulGsp c M) = (c : F) * c * mu M := by
  have h : (gm (smulGsp c M))ᵀ * formJ 2 F * gm (smulGsp c M) =
      (((c * c * multiplier 2 F M : Fˣ)) : F) • formJ 2 F := by
    rw [gm_smulGsp]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show formJ 2 F = gram F 2 from rfl, gm_transpose_mul, smul_smul, Units.val_mul,
      Units.val_mul]
  rw [mu, multiplier_eq _ h, Units.val_mul, Units.val_mul]

theorem conjSp_smulGsp (c : Fˣ) (M : gsp 2 F) (x : StatedSp 2 F) :
    conjSp 2 F (smulGsp c M) x = conjSp 2 F M x := by
  apply Subtype.ext
  rw [coe_conjSp, coe_conjSp]
  have hcc : ∀ y : GL (Fin 2 ⊕ Fin 2) F,
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c * y =
        y * Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := fun y => by
    have : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈
        Subgroup.center (GL (Fin 2 ⊕ Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.mem_center_iff.mp this y).symm
  change Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c * (M : GL _ F) * (x : GL _ F) *
    (Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c * (M : GL _ F))⁻¹ = _
  set s := Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c
  calc s * (M : GL _ F) * (x : GL _ F) * (s * (M : GL _ F))⁻¹ =
      s * ((M : GL _ F) * (x : GL _ F) * (M : GL _ F)⁻¹) * s⁻¹ := by group
    _ = (M : GL _ F) * (x : GL _ F) * (M : GL _ F)⁻¹ * s * s⁻¹ := by rw [hcc]
    _ = (M : GL _ F) * (x : GL _ F) * (M : GL _ F)⁻¹ := by group

theorem pow_half_eq_neg_one [Fintype F] (hF : ringChar F ≠ 2) {x : F} (hx : x ≠ 0)
    (hns : ¬ IsSquare x) : x ^ (Fintype.card F / 2) = -1 := by
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have h1 : x ^ (Fintype.card F / 2) * x ^ (Fintype.card F / 2) = 1 := by
    rw [← pow_add, ← two_mul, show 2 * (Fintype.card F / 2) = Fintype.card F - 1 by omega]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  rcases mul_self_eq_one_iff.mp h1 with h | h
  · exact absurd ((FiniteField.isSquare_iff hF hx).mpr h) hns
  · exact h

theorem exists_unit_mul_self_mul [Finite F] (h2 : (2 : F) ≠ 0) {μ₁ μ₂ : F} (h₁ : μ₁ ≠ 0)
    (h₂ : μ₂ ≠ 0) (hns₁ : ¬ IsSquare μ₁) (hns₂ : ¬ IsSquare μ₂) :
    ∃ c : Fˣ, (c : F) * c * μ₂ = μ₁ := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hF := C25W.Sp.ringChar_ne_two_of_two_ne_zero h2
  have hq : IsSquare (μ₁ / μ₂) := by
    rw [FiniteField.isSquare_iff hF (div_ne_zero h₁ h₂), div_pow, pow_half_eq_neg_one hF h₁ hns₁,
      pow_half_eq_neg_one hF h₂ hns₂, div_self (by norm_num)]
  obtain ⟨r, hr⟩ := hq
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hr
    rcases hr with h | h
    · exact h₁ h
    · exact h₂ h
  refine ⟨Units.mk0 r hr0, ?_⟩
  rw [Units.val_mk0, ← hr, div_mul_cancel₀ _ h₂]

theorem conjSp_eq_of_intertwine (M M' : gsp 2 F) (h : StatedSp 2 F)
    (hM : gm M' * mat 2 F h = mat 2 F h * gm M) (x : StatedSp 2 F) :
    conjSp 2 F M' x = h * conjSp 2 F M (h⁻¹ * x * h) * h⁻¹ := by
  have hGL : (M' : GL (Fin 2 ⊕ Fin 2) F) = (h : GL _ F) * (M : GL _ F) * (h : GL _ F)⁻¹ := by
    apply Units.ext
    have e : gm M' = mat 2 F h * gm M * mat 2 F h⁻¹ := by
      rw [← hM, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul]
    exact e
  apply Subtype.ext
  rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, coe_conjSp, hGL]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

end CFSG.ClassicalInvolution.Asc77.C5O.M
