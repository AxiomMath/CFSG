module

public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS7

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_zero_of_two_smul_eq_zero (h2 : (2 : K) ≠ 0) {v : V} (h : (2 : K) • v = 0) : v = 0 :=
  (smul_eq_zero.mp h).resolve_left h2

theorem eq_zero_of_range_le_eigen (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1)
    {L : V →ₗ[K] V} (hwL : ∀ y, w (L y) = -L (w y))
    (hker : ∀ y, L y = 0 → ∀ z, polar Q y (L z) = 0) {δ : K} (hδ : δ * δ = 1)
    (hLδ : ∀ y, w (L y) = δ • L y) : L = 0 := by
  have hδ0 : δ ≠ 0 := fun h => by rw [h, mul_zero] at hδ; exact zero_ne_one hδ
  have hww : ∀ y, w (w y) = y := fun y => by
    have := congrArg (fun m : V ≃ₗ[K] V => m y) hw2
    simpa using this
  refine LinearMap.ext fun z => ?_
  refine eq_zero_of_polar_eq_zero hQ fun y => ?_
  set a : V := y + δ • w y with ha
  set b : V := y - δ • w y with hb
  have hwa : w a = δ • a := by
    rw [ha, map_add, map_smul, hww]
    calc w y + δ • y = δ • y + (δ * δ) • w y := by rw [hδ, one_smul]; module
      _ = δ • (y + δ • w y) := by module
  have hwb : w b = (-δ) • b := by
    rw [hb, map_sub, map_smul, hww]
    calc w y - δ • y = (-δ) • y + (δ * δ) • w y := by rw [hδ, one_smul]; module
      _ = (-δ) • (y - δ • w y) := by module
  have hLa : L a = 0 := by
    have h1 := hLδ a
    have h2' := hwL a
    rw [hwa, map_smul] at h2'
    have h3 : (2 : K) • (δ • L a) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h1]
      rw [h2']
      simp
    have h4 := eq_zero_of_two_smul_eq_zero h2 h3
    exact (smul_eq_zero.mp h4).resolve_left hδ0
  have hpa : polar Q (L z) a = 0 := by
    rw [polar_comm]
    exact hker a hLa z
  have hpb : polar Q (L z) b = 0 := by
    have h1 := polar_map_of_mem hwO (L z) b
    rw [hwb, hLδ, polar_smul_left_eq, polar_smul_right_eq] at h1
    have h3 : (2 : K) * polar Q (L z) b = 0 := by
      have : δ * ((-δ) * polar Q (L z) b) = polar Q (L z) b := h1
      linear_combination (-1 : K) * this - (polar Q (L z) b) * hδ
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hsum : (2 : K) * polar Q (L z) y = 0 := by
    have : (2 : K) • y = a + b := by
      rw [ha, hb, two_smul]
      abel
    have h4 := congrArg (polar Q (L z)) this
    rw [polar_add_right, hpa, hpb, polar_smul_right_eq] at h4
    simpa using h4
  exact (mul_eq_zero.mp hsum).resolve_left h2

theorem exists_eigen_in_range (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1)
    {L : V →ₗ[K] V} (hwL : ∀ y, w (L y) = -L (w y))
    (hker : ∀ y, L y = 0 → ∀ z, polar Q y (L z) = 0) (hL0 : L ≠ 0) {δ : K} (hδ : δ * δ = 1) :
    ∃ u ∈ LinearMap.range L, u ≠ 0 ∧ w u = δ • u := by
  have hδ0 : δ ≠ 0 := fun h => by rw [h, mul_zero] at hδ; exact zero_ne_one hδ
  have hww : ∀ y, w (w y) = y := fun y => by
    have := congrArg (fun m : V ≃ₗ[K] V => m y) hw2
    simpa using this
  have hwr : ∀ v ∈ LinearMap.range L, w v ∈ LinearMap.range L := by
    rintro _ ⟨y, rfl⟩
    exact ⟨-w y, by rw [hwL, map_neg]⟩
  by_contra hno
  push Not at hno
  refine hL0 (eq_zero_of_range_le_eigen h2 hQ hwO hw2 hwL hker (δ := -δ) (by rw [neg_mul_neg, hδ])
    fun y => ?_)
  set v := L y with hv
  have hvr : v ∈ LinearMap.range L := ⟨y, rfl⟩
  have hu : v + δ • w v ∈ LinearMap.range L := Submodule.add_mem _ hvr
    (Submodule.smul_mem _ _ (hwr v hvr))
  have hwu : w (v + δ • w v) = δ • (v + δ • w v) := by
    rw [map_add, map_smul, hww, smul_add, smul_smul, hδ, one_smul, add_comm]
  have h0 : v + δ • w v = 0 := by
    by_contra hne
    exact hno _ hu hne hwu
  have h1 : δ • w v = -v := eq_neg_of_add_eq_zero_right h0
  calc w v = δ • (δ • w v) := by rw [smul_smul, hδ, one_smul]
    _ = (-δ) • v := by rw [h1, smul_neg, neg_smul]

theorem exists_singular_eigenvectors (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {w : V ≃ₗ[K] V} (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hw2 : w * w = 1)
    {L : V →ₗ[K] V} (hwL : ∀ y, w (L y) = -L (w y)) (hsing : ∀ y, Q (L y) = 0)
    (hker : ∀ y, L y = 0 → ∀ z, polar Q y (L z) = 0) (hL0 : L ≠ 0) :
    ∃ up um : V, up ∈ LinearMap.range L ∧ um ∈ LinearMap.range L ∧ up ≠ 0 ∧ um ≠ 0 ∧
      w up = up ∧ w um = -um ∧ Q up = 0 ∧ Q um = 0 := by
  obtain ⟨up, hup, hnep, hwp⟩ := exists_eigen_in_range h2 hQ hwO hw2 hwL hker hL0 (δ := 1)
    (one_mul 1)
  obtain ⟨um, hum, hnem, hwm⟩ := exists_eigen_in_range h2 hQ hwO hw2 hwL hker hL0 (δ := -1)
    (by norm_num)
  refine ⟨up, um, hup, hum, hnep, hnem, by simpa using hwp, by simpa using hwm, ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hup
    exact hsing y
  · obtain ⟨y, rfl⟩ := hum
    exact hsing y

end CFSG.ClassicalInvolution.RouteD.TWS7
