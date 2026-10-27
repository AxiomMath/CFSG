module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Mat2
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem om6par_span (Z : Mat2) :
    ∃ c₁ c₂ c₃ c₄ : ZMod 3, Z = c₁ • (1 : Mat2) + c₂ • !![1, 1; 0, 1] + c₃ • !![1, 0; 1, 1] +
      c₄ • !![1, 1; -1, 0] := by
  refine ⟨-Z 0 1 - Z 1 0 + Z 1 1, Z 0 1 - Z 0 0 + Z 1 1, Z 1 0 + Z 0 0 - Z 1 1, Z 0 0 - Z 1 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem om6par_basis_sl :
    ∃ a b w : SL2F3, (a : Mat2) = !![1, 1; 0, 1] ∧ (b : Mat2) = !![1, 0; 1, 1] ∧
      (w : Mat2) = !![1, 1; -1, 0] :=
  ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩,
    ⟨!![1, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, rfl, rfl, rfl⟩

theorem om6par_mat2_form (σ : Mat2 ≃ₗ[ZMod 3] Mat2) {μ : ZMod 3} (hμ : μ ≠ 0)
    (hdet : ∀ X : Mat2, (σ X).det = μ * X.det)
    (hL : ∀ A : SL2F3, ∃ A' : SL2F3, ∀ X : Mat2, σ ((A : Mat2) * X) = (A' : Mat2) * σ X) :
    ∃ g : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ, ∀ X : Mat2,
      σ X = (g : Mat2) * X * ((g⁻¹ : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ) : Mat2) * σ 1 := by
  have hpdet : (σ 1).det = μ := by rw [hdet, Matrix.det_one, mul_one]
  have hpu : IsUnit (σ 1) := (Matrix.isUnit_iff_isUnit_det _).mpr (by
    rw [hpdet]; exact IsUnit.mk0 _ hμ)
  obtain ⟨u, hu⟩ := hpu
  let ρ : Mat2 ≃ₗ[ZMod 3] Mat2 :=
    LinearEquiv.ofLinear (LinearMap.mulRight (ZMod 3) ((u⁻¹ : Mat2ˣ) : Mat2))
      (LinearMap.mulRight (ZMod 3) (u : Mat2))
      (by
        ext X : 1
        simp [Matrix.mul_assoc])
      (by
        ext X : 1
        simp [Matrix.mul_assoc])
  let τ : Mat2 ≃ₗ[ZMod 3] Mat2 := σ.trans ρ
  have hτ : ∀ X, τ X = σ X * ((u⁻¹ : Mat2ˣ) : Mat2) := fun X => rfl
  have hτ1 : τ 1 = 1 := by rw [hτ, ← hu, Units.mul_inv]
  have hτL : ∀ A : SL2F3, ∀ Y : Mat2, τ ((A : Mat2) * Y) = τ (A : Mat2) * τ Y := by
    intro A Y
    obtain ⟨A', hA'⟩ := hL A
    have h1 : σ (A : Mat2) = (A' : Mat2) * σ 1 := by
      have := hA' 1
      rwa [Matrix.mul_one] at this
    have h2 : τ (A : Mat2) = (A' : Mat2) := by
      rw [hτ, h1, Matrix.mul_assoc, ← hu, Units.mul_inv, Matrix.mul_one]
    rw [h2, hτ, hτ, hA' Y, Matrix.mul_assoc]
  obtain ⟨a, b, w, ha, hb, hw⟩ := om6par_basis_sl
  have hτmul : ∀ Z Y : Mat2, τ (Z * Y) = τ Z * τ Y := by
    intro Z Y
    obtain ⟨c₁, c₂, c₃, c₄, rfl⟩ := om6par_span Z
    have e1 : τ ((1 : Mat2) * Y) = τ (1 : Mat2) * τ Y := by
      rw [hτ1, Matrix.one_mul, Matrix.one_mul]
    have e2 := hτL a Y
    have e3 := hτL b Y
    have e4 := hτL w Y
    rw [ha] at e2
    rw [hb] at e3
    rw [hw] at e4
    simp only [Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, e1, e2, e3, e4]
  let τa : Mat2 ≃ₐ[ZMod 3] Mat2 := AlgEquiv.ofLinearEquiv τ hτ1 hτmul
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.innerAut_surjective (n := Fin 2) (ZMod 3) τa
  refine ⟨g, fun X => ?_⟩
  have h1 : τ X = (g : Mat2) * X * ((g⁻¹ : Mat2ˣ) : Mat2) := by
    have h0 : τa X = τ X := rfl
    have h3 := congrArg (fun e : Mat2 ≃ₐ[ZMod 3] Mat2 => e X) hg
    simp only [Matrix.GeneralLinearGroup.innerAut_apply] at h3
    rw [← h0, ← h3, Matrix.coe_units_inv]
  have h2 : σ X = τ X * σ 1 := by
    rw [hτ, Matrix.mul_assoc, ← hu, Units.inv_mul, Matrix.mul_one]
  rw [h2, h1]

theorem om6par_comm_four : ∀ g h : Mat2, g * h = 1 →
    ((∃ s : SL2F3, ¬ (h * (s : Mat2) * g * ((s⁻¹ : SL2F3) : Mat2)) ^ 4 = 1) ↔ g.det = -1) := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
