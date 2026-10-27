module

public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessNorm

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_conj_of_unit_plane_actions
    (Q : QuadraticForm K V) (h2 : (2 : K) ≠ 0)
    (s t : TauCeti.QuadraticMap.orthogonalGroup Q)
    {u v u' v' : V}
    (hu : Q u = 1) (hv : Q v = 1)
    (huv : Q.polarBilin u v = 0)
    (hu' : Q u' = 1) (hv' : Q v' = 1)
    (huv' : Q.polarBilin u' v' = 0)
    (hsu : (s : V ≃ₗ[K] V) u = -u)
    (hsv : (s : V ≃ₗ[K] V) v = -v)
    (hsfix : ∀ x : V, Q.polarBilin u x = 0 → Q.polarBilin v x = 0 →
      (s : V ≃ₗ[K] V) x = x)
    (htu : (t : V ≃ₗ[K] V) u' = -u')
    (htv : (t : V ≃ₗ[K] V) v' = -v')
    (htfix : ∀ x : V, Q.polarBilin u' x = 0 → Q.polarBilin v' x = 0 →
      (t : V ≃ₗ[K] V) x = x) :
    ∃ g : TauCeti.QuadraticMap.orthogonalGroup Q,
      (g : V ≃ₗ[K] V) u = u' ∧ (g : V ≃ₗ[K] V) v = v' ∧
      g * s * g⁻¹ = t := by
  have huvP : polar Q u v = 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using huv
  have huv'P : polar Q u' v' = 0 := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using huv'
  obtain ⟨k, hk, hku, hkv⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonalD4.exists_isometry_pair h2 Q hu hv huvP hu' hv' huv'P
  let g : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨k, hk⟩
  let c : TauCeti.QuadraticMap.orthogonalGroup Q := g * s * g⁻¹
  have hc_coe : (c : V ≃ₗ[K] V) = k * (s : V ≃ₗ[K] V) * k⁻¹ := rfl
  have hcu' : (c : V ≃ₗ[K] V) u' = -u' := by
    rw [hc_coe, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show k⁻¹ u' = u by rw [← hku, LinearEquiv.inv_apply_apply'], hsu, map_neg, hku]
  have hcv' : (c : V ≃ₗ[K] V) v' = -v' := by
    rw [hc_coe, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show k⁻¹ v' = v by rw [← hkv, LinearEquiv.inv_apply_apply'], hsv, map_neg, hkv]
  have hcvu : polar Q v' u' = 0 := by
    rw [polar_comm]
    exact huv'P
  have hcfix : ∀ x : V, polar Q u' x = 0 → polar Q v' x = 0 →
      (c : V ≃ₗ[K] V) x = x := by
    intro x hx hx'
    have h1 : polar Q u (k⁻¹ x) = 0 := by
      have h := polar_map_of_mem hk u (k⁻¹ x)
      rw [hku, LinearEquiv.apply_inv_apply'] at h
      rw [← h]
      exact hx
    have h2 : polar Q v (k⁻¹ x) = 0 := by
      have h := polar_map_of_mem hk v (k⁻¹ x)
      rw [hkv, LinearEquiv.apply_inv_apply'] at h
      rw [← h]
      exact hx'
    rw [hc_coe, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hsfix (k⁻¹ x) (by simpa only [QuadraticMap.polarBilin_apply_apply] using h1)
        (by simpa only [QuadraticMap.polarBilin_apply_apply] using h2),
      LinearEquiv.apply_inv_apply']
  have h_eq_of_actions : ∀ f : V ≃ₗ[K] V, f u' = -u' → f v' = -v' →
      (∀ z : V, polar Q u' z = 0 → polar Q v' z = 0 → f z = z) →
      (c : V ≃ₗ[K] V) = f := by
    intro f hfu hfv hffix
    apply LinearEquiv.ext
    intro x
    let a : K := polar Q u' x / 2
    let b : K := polar Q v' x / 2
    have ha : a * 2 = polar Q u' x := by
      dsimp only [a]
      exact div_mul_cancel₀ _ h2
    have hb : b * 2 = polar Q v' x := by
      dsimp only [b]
      exact div_mul_cancel₀ _ h2
    have huu : polar Q u' u' = 2 := by
      rw [polar_self_eq_two_mul, hu', mul_one]
    have hvv : polar Q v' v' = 2 := by
      rw [polar_self_eq_two_mul, hv', mul_one]
    let r : V := x - a • u' - b • v'
    have hru : polar Q u' r = 0 := by
      dsimp only [r]
      rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        huu, huv'P, mul_zero, sub_zero, ha, sub_self]
    have hrv : polar Q v' r = 0 := by
      dsimp only [r]
      rw [polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
        hcvu, hvv, mul_zero, sub_zero, hb, sub_self]
    have hdec : a • u' + b • v' + r = x := by
      dsimp only [r]
      abel
    have hact_c : (c : V ≃ₗ[K] V) x = -a • u' - b • v' + r := by
      rw [← hdec, map_add, map_add, map_smul, map_smul, hcu', hcv', hcfix r hru hrv]
      simp only [smul_neg, neg_smul]
      abel
    have hact_f : f x = -a • u' - b • v' + r := by
      rw [← hdec, map_add, map_add, map_smul, map_smul, hfu, hfv, hffix r hru hrv]
      simp only [smul_neg, neg_smul]
      abel
    rw [hact_c, hact_f]
  have hct : c = t :=
    Subtype.ext (h_eq_of_actions (t : V ≃ₗ[K] V) htu htv
      (fun z hz hz' => htfix z (by simpa only [QuadraticMap.polarBilin_apply_apply] using hz)
        (by simpa only [QuadraticMap.polarBilin_apply_apply] using hz')))
  exact ⟨g, hku, hkv, hct⟩

end CFSG.ClassicalGroups.Orthogonal
