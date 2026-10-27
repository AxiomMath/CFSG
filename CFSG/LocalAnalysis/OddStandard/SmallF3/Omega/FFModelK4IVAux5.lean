module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IIIAux5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_k4iv_reflOf_neg {u : V} (hu : Q u ≠ 0) (hmu : Q (-u) ≠ 0) :
    reflOf Q (-u) hmu = reflOf Q u hu := by
  letI : Invertible (Q u) := invertibleOfNonzero hu
  letI : Invertible (Q (-u)) := invertibleOfNonzero hmu
  apply Subtype.ext; apply LinearEquiv.ext; intro x
  rw [coe_reflOf_apply (-u) hmu, coe_reflOf_apply u hu]
  congr 1
  simp only [QuadraticMap.polar_neg_left, QuadraticMap.map_neg, neg_div, smul_neg, neg_neg]
  module

noncomputable def reflTot (Q : QuadraticForm (ZMod 3) V) (u : V) : OGroup Q :=
  if h : Q u ≠ 0 then reflOf Q u h else 1

theorem reflTot_of_ne {u : V} (hu : Q u ≠ 0) : reflTot Q u = reflOf Q u hu := by
  unfold reflTot; rw [dif_pos hu]

theorem reflTot_of_eq {u : V} (hu : Q u = 0) : reflTot Q u = 1 := by
  unfold reflTot; rw [dif_neg (not_not.mpr hu)]

theorem coe_reflTot_apply (u x : V) :
    ((reflTot Q u : OGroup Q) : V ≃ₗ[ZMod 3] V) x = x - (polar Q u x / Q u) • u := by
  by_cases hu : Q u = 0
  · rw [reflTot_of_eq hu, hu]; simp
  · rw [reflTot_of_ne hu, coe_reflOf_apply u hu x]

theorem reflTot_neg (u : V) : reflTot Q (-u) = reflTot Q u := by
  by_cases hu : Q u = 0
  · rw [reflTot_of_eq hu, reflTot_of_eq (by rw [QuadraticMap.map_neg]; exact hu)]
  · have hmu : Q (-u) ≠ 0 := by rwa [QuadraticMap.map_neg]
    rw [reflTot_of_ne hu, reflTot_of_ne hmu]; exact ff_k4iv_reflOf_neg hu hmu

theorem reflTot_mul_self (u : V) : reflTot Q u * reflTot Q u = 1 := by
  by_cases hu : Q u = 0
  · rw [reflTot_of_eq hu, one_mul]
  · rw [reflTot_of_ne hu]; exact reflOf_mul_self u hu

theorem reflTot_inv (u : V) : (reflTot Q u)⁻¹ = reflTot Q u :=
  inv_eq_of_mul_eq_one_left (reflTot_mul_self u)

theorem reflTot_conj (g : OGroup Q) (u : V) :
    g * reflTot Q u * g⁻¹ = reflTot Q ((g : V ≃ₗ[ZMod 3] V) u) := by
  by_cases hu : Q u = 0
  · have hgu : Q ((g : V ≃ₗ[ZMod 3] V) u) = 0 := by rwa [map_ogroup_apply]
    rw [reflTot_of_eq hu, reflTot_of_eq hgu]; group
  · have hgu : Q ((g : V ≃ₗ[ZMod 3] V) u) ≠ 0 := by rwa [map_ogroup_apply]
    rw [reflTot_of_ne hu, mul_reflOf_mul_inv g u hu, reflTot_of_ne hgu]

theorem reflTot_comm {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0) (huv : polar Q u v = 0) :
    reflTot Q u * reflTot Q v = reflTot Q v * reflTot Q u := by
  rw [reflTot_of_ne hu, reflTot_of_ne hv]; exact ff_k4iv_reflOf_comm hu hv huv

theorem simAct_reflTot {ρ : ↥(simGroup Q)} (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (u : V) : simAct Q ρ (reflTot Q u) = reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u) := by
  by_cases hu : Q u = 0
  · have hρu : Q ((ρ : V ≃ₗ[ZMod 3] V) u) = 0 := by rw [hρ u, hu]; simp
    rw [reflTot_of_eq hu, reflTot_of_eq hρu, map_one]
  · have hρu : Q ((ρ : V ≃ₗ[ZMod 3] V) u) ≠ 0 := by
      rw [hρ u]; exact mul_ne_zero (by decide) hu
    rw [reflTot_of_ne hu, ff_simAct_reflOf hρ u hu, reflTot_of_ne hρu]

section KData

variable {R : V ≃ₗ[ZMod 3] V} {u₁ u₂ : V}

theorem ff_k4iv_polar_sim (hR : IsSimilitude Q R (-1)) (x y : V) :
    polar Q (R x) (R y) = - polar Q x y := by
  have := ff_k4iv_polar_isSimilitude_neg (Q := Q) hR x y
  simpa only [QuadraticMap.polarBilin_apply_apply] using this

theorem ff_k4iv_map_sim (hR : IsSimilitude Q R (-1)) (x : V) : Q (R x) = - Q x := by
  rw [hR x]; simp

theorem ff_k4iv_Q_diff (hu₁ : Q u₁ = 1) (hu₂ : Q u₂ = 1) (h12 : polar Q u₁ u₂ = 0) :
    Q (u₁ - u₂) = 2 := by
  rw [ff_map_sub, hu₁, hu₂, h12]; decide

theorem ff_k4iv_polar_diff (hu₁ : Q u₁ = 1) (h12 : polar Q u₁ u₂ = 0) :
    polar Q (u₁ - u₂) u₁ = 2 := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self, QuadraticMap.polar_comm Q u₂ u₁, h12,
    hu₁]
  decide

theorem ff_k4iv_sigma_u1 (hu₁ : Q u₁ = 1) (hu₂ : Q u₂ = 1) (h12 : polar Q u₁ u₂ = 0)
    (hR : IsSimilitude Q R (-1)) (h1R1 : polar Q u₁ (R u₁) = 0) (h1R2 : polar Q u₁ (R u₂) = 0) :
    ((reflTot Q (u₁ - u₂) * reflTot Q (R (u₁ - u₂)) : OGroup Q) : V ≃ₗ[ZMod 3] V) u₁ = u₂ := by
  have h0 : polar Q (R (u₁ - u₂)) u₁ = 0 := by
    rw [map_sub, QuadraticMap.polar_sub_left, QuadraticMap.polar_comm Q (R u₁) u₁,
      QuadraticMap.polar_comm Q (R u₂) u₁, h1R1, h1R2]
    simp
  have h1 : ((reflTot Q (R (u₁ - u₂)) : OGroup Q) : V ≃ₗ[ZMod 3] V) u₁ = u₁ := by
    rw [coe_reflTot_apply, h0]; simp
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h1, coe_reflTot_apply, ff_k4iv_polar_diff hu₁ h12,
    ff_k4iv_Q_diff hu₁ hu₂ h12]
  have hdiv : (2 : ZMod 3) / 2 = 1 := div_self (by decide)
  rw [hdiv, one_smul]
  abel

theorem ff_k4iv_sigma_Ru1 (hu₁ : Q u₁ = 1) (hu₂ : Q u₂ = 1) (h12 : polar Q u₁ u₂ = 0)
    (hR : IsSimilitude Q R (-1)) (h1R2 : polar Q u₁ (R u₂) = 0)
    (h2R2 : polar Q u₂ (R u₂) = 0) :
    ((reflTot Q (u₁ - u₂) * reflTot Q (R (u₁ - u₂)) : OGroup Q) : V ≃ₗ[ZMod 3] V) (R u₁) =
      R u₂ := by
  have hQRv : Q (R (u₁ - u₂)) = 1 := by
    rw [ff_k4iv_map_sim hR, ff_k4iv_Q_diff hu₁ hu₂ h12]; decide
  have hpRR : polar Q (R (u₁ - u₂)) (R u₁) = 1 := by
    rw [ff_k4iv_polar_sim hR, ff_k4iv_polar_diff hu₁ h12]; decide
  have h1 : ((reflTot Q (R (u₁ - u₂)) : OGroup Q) : V ≃ₗ[ZMod 3] V) (R u₁) = R u₂ := by
    rw [coe_reflTot_apply, hpRR, hQRv, div_one, one_smul, map_sub]
    abel
  have h3 : polar Q (u₁ - u₂) (R u₂) = 0 := by
    rw [QuadraticMap.polar_sub_left, h1R2, h2R2]; simp
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply, h1, coe_reflTot_apply, h3, zero_div, zero_smul,
    sub_zero]

theorem ff_k4iv_conj_d (hu₁ : Q u₁ = 1) (hu₂ : Q u₂ = 1) (h12 : polar Q u₁ u₂ = 0)
    (hR : IsSimilitude Q R (-1)) (h1R1 : polar Q u₁ (R u₁) = 0) (h1R2 : polar Q u₁ (R u₂) = 0)
    (h2R2 : polar Q u₂ (R u₂) = 0) :
    (reflTot Q (u₁ - u₂) * reflTot Q (R (u₁ - u₂))) * (reflTot Q u₁ * reflTot Q (R u₁)) *
      (reflTot Q (u₁ - u₂) * reflTot Q (R (u₁ - u₂)))⁻¹ =
        reflTot Q u₂ * reflTot Q (R u₂) := by
  set σ : OGroup Q := reflTot Q (u₁ - u₂) * reflTot Q (R (u₁ - u₂)) with hσ
  have e1 := reflTot_conj σ u₁
  have e2 := reflTot_conj σ (R u₁)
  rw [hσ, ff_k4iv_sigma_u1 hu₁ hu₂ h12 hR h1R1 h1R2] at e1
  rw [hσ, ff_k4iv_sigma_Ru1 hu₁ hu₂ h12 hR h1R2 h2R2] at e2
  calc σ * (reflTot Q u₁ * reflTot Q (R u₁)) * σ⁻¹
      = (σ * reflTot Q u₁ * σ⁻¹) * (σ * reflTot Q (R u₁) * σ⁻¹) := by group
    _ = reflTot Q u₂ * reflTot Q (R u₂) := by rw [hσ, e1, e2]

theorem ff_k4iv_dinv (hR : IsSimilitude Q R (-1)) {u : V} (hu : Q u ≠ 0)
    (hup : polar Q u (R u) = 0) :
    (reflTot Q u * reflTot Q (R u))⁻¹ = reflTot Q u * reflTot Q (R u) := by
  have hRu : Q (R u) ≠ 0 := by rw [ff_k4iv_map_sim hR]; exact neg_ne_zero.mpr hu
  rw [mul_inv_rev, reflTot_inv, reflTot_inv]
  exact (reflTot_comm hu hRu hup).symm

end KData

end CFSG.OddStandard.SmallF3.Omega
