module

public import CFSG.ClassicalInvolution.Phan.PhanS9WRefl

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap

section Det

variable {F : Type} [Field F] [Invertible (2 : F)] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

theorem orthogonalDet_eq_one_or_neg_one {Q : QuadraticForm F V} (hQ : Q.Nondegenerate)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    QuadraticMap.orthogonalDet Q g = 1 ∨ QuadraticMap.orthogonalDet Q g = -1 := by
  have hsq := TauCeti.QuadraticMap.orthogonalDet_sq
    ((QuadraticMap.nondegenerate_polar_iff.mpr hQ).1) g
  have hsq' : ((QuadraticMap.orthogonalDet Q g : Fˣ) : F) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
  rcases sq_eq_one_iff.mp hsq' with h | h
  · exact Or.inl (Units.ext (by simpa using h))
  · exact Or.inr (Units.ext (by simpa using h))

theorem exists_det_one_move {Q : QuadraticForm F V} (hQ : Q.Nondegenerate)
    (g₀ : TauCeti.QuadraticMap.orthogonalGroup Q) {R : Submodule F V} {a b a' b' n : V}
    (hR : ∀ r ∈ R, (g₀ : V ≃ₗ[F] V) r = r) (ha : (g₀ : V ≃ₗ[F] V) a = a')
    (hb : (g₀ : V ≃ₗ[F] V) b = b') (hn : Q n ≠ 0) (hnR : ∀ r ∈ R, polar Q r n = 0)
    (hna : polar Q a' n = 0) (hnb : polar Q b' n = 0) :
    ∃ g₁ : TauCeti.QuadraticMap.orthogonalGroup Q, (∀ r ∈ R, (g₁ : V ≃ₗ[F] V) r = r) ∧
      (g₁ : V ≃ₗ[F] V) a = a' ∧ (g₁ : V ≃ₗ[F] V) b = b' ∧
      QuadraticMap.orthogonalDet Q g₁ = 1 := by
  rcases orthogonalDet_eq_one_or_neg_one hQ g₀ with hd | hd
  · exact ⟨g₀, hR, ha, hb, hd⟩
  · have := invertibleOfNonzero hn
    have hfix : ∀ z, polar Q n z = 0 → TauCeti.QuadraticMap.reflection Q n z = z := fun z hz =>
      TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero Q n hz
    refine ⟨TauCeti.QuadraticMap.reflectionOrthogonal Q n * g₀, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hR r hr,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        hfix r (by rw [QuadraticMap.polar_comm]; exact hnR r hr)]
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ha,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        hfix a' (by rw [QuadraticMap.polar_comm]; exact hna)]
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hb,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        hfix b' (by rw [QuadraticMap.polar_comm]; exact hnb)]
    · rw [map_mul, QuadraticMap.orthogonalDet_reflectionOrthogonal, hd]
      norm_num

end Det

section Rotation

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Invertible (2 : F)] (D : KDat F K)

theorem exists_rotation_correction [Finite F] (hodd : Odd (Nat.card F))
    (hQ : (quadOdd 3 F).Nondegenerate) {R : Submodule F (W7 F)} {α : F} (hα : α ≠ 0)
    {a b : W7 F} (hRa : ∀ r ∈ R, polar (quadOdd 3 F) r a = 0)
    (hRb : ∀ r ∈ R, polar (quadOdd 3 F) r b = 0) (hab : polar (quadOdd 3 F) a b = 0)
    (ha : quadOdd 3 F a = α) (hb : quadOdd 3 F b = α)
    (σ : Multiplicative (TauCeti.SquareClassGroup F)) :
    ∃ h : TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 F),
      (∀ r ∈ R, (h : W7 F ≃ₗ[F] W7 F) r = r) ∧
      QuadraticMap.orthogonalDet (quadOdd 3 F) h = 1 ∧
      CliffordAlgebra.orthogonalSpinorNorm (quadOdd 3 F) hQ h = σ ∧
      ∃ c : K, c ≠ 0 ∧ extK (K := K) (h : W7 F ≃ₗ[F] W7 F).toLinearMap (emb a + D.θ • emb b) =
        c • (emb a + D.θ • emb b) := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, TauCeti.squareClassHom u = σ := by
    refine ⟨Additive.toMul (Quotient.out (Multiplicative.toAdd σ)), ?_⟩
    rw [TauCeti.squareClassHom_apply, TauCeti.squareClass_toMul_out]
    rfl
  obtain ⟨s, t, hst⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hcard hα hα
    (α⁻¹ * (u : F))
  obtain ⟨w, hw⟩ : ∃ w : W7 F, w = s • a + t • b := ⟨_, rfl⟩
  have hQw' : quadOdd 3 F w = α * (s ^ 2 + t ^ 2) := by
    rw [hw, CFSG.RankThree.Classical.quad_smul_add_smul _ hab, ha, hb]
    ring
  have hQw : quadOdd 3 F w = α⁻¹ * (u : F) := by
    rw [hQw']
    linear_combination hst
  have hQw0 : quadOdd 3 F w ≠ 0 := by
    rw [hQw]
    exact mul_ne_zero (inv_ne_zero hα) u.ne_zero
  have hn : s ^ 2 + t ^ 2 ≠ 0 := by
    intro h
    apply hQw0
    rw [hQw', h, mul_zero]
  have hia : Invertible (quadOdd 3 F a) := invertibleOfNonzero (by rw [ha]; exact hα)
  have hiw : Invertible (quadOdd 3 F w) := invertibleOfNonzero hQw0
  have hwR : ∀ r ∈ R, polar (quadOdd 3 F) w r = 0 := fun r hr => by
    rw [hw, polar_add_left, polar_smul_left, polar_smul_left, QuadraticMap.polar_comm _ a r,
      QuadraticMap.polar_comm _ b r, hRa r hr, hRb r hr]
    simp
  have hfixw : ∀ r ∈ R, TauCeti.QuadraticMap.reflection (quadOdd 3 F) w r = r := fun r hr =>
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ w (hwR r hr)
  have hfixa : ∀ r ∈ R, TauCeti.QuadraticMap.reflection (quadOdd 3 F) a r = r := fun r hr =>
    TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero _ a (by
      rw [QuadraticMap.polar_comm]
      exact hRa r hr)
  refine ⟨TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 3 F) a *
    TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 3 F) w, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_mul, LinearEquiv.mul_apply, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
      TauCeti.QuadraticMap.coe_reflectionOrthogonal, hfixw r hr, hfixa r hr]
  · rw [map_mul, QuadraticMap.orthogonalDet_reflectionOrthogonal,
      QuadraticMap.orthogonalDet_reflectionOrthogonal]
    norm_num
  · have hU : unitOfInvertible (quadOdd 3 F a) * unitOfInvertible (quadOdd 3 F w) = u := by
      refine Units.ext ?_
      rw [Units.val_mul, val_unitOfInvertible, val_unitOfInvertible, ha, hQw]
      field_simp
    rw [map_mul, CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal,
      CliffordAlgebra.orthogonalSpinorNorm_reflectionOrthogonal, ← hu, ← hU, map_mul]
  · obtain ⟨c, hc, hcx⟩ := extK_reflection_pair D hab ha hb hα hn hw
    refine ⟨c, hc, ?_⟩
    have hcoe : ((TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 3 F) a *
        TauCeti.QuadraticMap.reflectionOrthogonal (quadOdd 3 F) w :
          TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 F)) : W7 F ≃ₗ[F] W7 F) =
        (TauCeti.QuadraticMap.reflection (quadOdd 3 F) a *
          TauCeti.QuadraticMap.reflection (quadOdd 3 F) w : W7 F ≃ₗ[F] W7 F) := by
      rw [Subgroup.coe_mul, TauCeti.QuadraticMap.coe_reflectionOrthogonal,
        TauCeti.QuadraticMap.coe_reflectionOrthogonal]
    rw [hcoe]
    exact hcx

end Rotation

end CFSG.ClassicalInvolution.PhanB3.S
