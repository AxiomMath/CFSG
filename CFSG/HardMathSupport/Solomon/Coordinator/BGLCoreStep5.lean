module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLCoreStep3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.LargeExtraspecial.A2Mod

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_not_fixed (h3 : orderOf σ = 3) : ∃ ν : F, σ ν ≠ ν := by
  by_contra h
  push Not at h
  exact sigma_ne_one h3 (RingEquiv.ext fun x => by rw [RingAut.one_apply]; exact h x)

theorem exists_norm_one (h3 : orderOf σ = 3) : ∃ l : F, σ l ≠ l ∧ l * σ l * σ (σ l) = 1 := by
  obtain ⟨ν, hν⟩ := exists_not_fixed h3
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h, map_zero])
  have hν1 : ν + 1 ≠ 0 := fun h => hν (by
    have : ν = -1 := by linear_combination h
    rw [this, map_neg, map_one])
  have hnorm : ∀ μ : F, μ ≠ 0 → (σ μ / μ) * σ (σ μ / μ) * σ (σ (σ μ / μ)) = 1 := by
    intro μ hμ
    have h1 : σ μ ≠ 0 := (map_ne_zero σ).mpr hμ
    have h2 : σ (σ μ) ≠ 0 := (map_ne_zero σ).mpr h1
    simp only [map_div₀, sigma_cube h3]
    field_simp
  by_cases hA : σ (σ ν / ν) = σ ν / ν
  · by_cases hB : σ (σ (ν + 1) / (ν + 1)) = σ (ν + 1) / (ν + 1)
    · exfalso
      have e1 : σ ν = σ ν / ν * ν := by field_simp
      have e2 : σ ν + 1 = σ (ν + 1) / (ν + 1) * (ν + 1) := by
        rw [map_add, map_one]
        field_simp
      set ρ := σ ν / ν
      set ρ' := σ (ν + 1) / (ν + 1)
      have hlin : (ρ - ρ') * ν = ρ' - 1 := by linear_combination e2 - e1
      by_cases hρρ : ρ = ρ'
      · have hρ'1 : ρ' = 1 := by
          rw [hρρ, sub_self, zero_mul] at hlin
          linear_combination -hlin
        apply hν
        rw [e1, hρρ, hρ'1, one_mul]
      · have hne : ρ - ρ' ≠ 0 := sub_ne_zero.mpr hρρ
        have hνeq : ν = (ρ' - 1) / (ρ - ρ') := by field_simp; linear_combination hlin
        apply hν
        rw [hνeq, map_div₀, map_sub, map_sub, map_one, hA, hB]
    · exact ⟨_, hB, hnorm _ hν1⟩
  · exact ⟨_, hA, hnorm _ hν0⟩

theorem cube_contra (h3 : orderOf σ = 3) {l : F} (hl : σ l ≠ l)
    (hn : l * σ l * σ (σ l) = 1) (hc : σ (l ^ 3) = l ^ 3) : False := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hn
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : F, ρ = σ l / l := ⟨_, rfl⟩
  have hσl : σ l = ρ * l := by rw [hρdef]; field_simp
  have hρ3 : ρ ^ 3 = 1 := by
    have h1 : (σ l) ^ 3 = l ^ 3 := by rw [← map_pow, hc]
    rw [hσl, mul_pow] at h1
    have h2 : (ρ ^ 3 - 1) * l ^ 3 = 0 := by linear_combination h1
    have := (mul_eq_zero.mp h2).resolve_right (pow_ne_zero 3 hl0)
    linear_combination this
  have hρ0 : ρ ≠ 0 := by
    rintro h0
    rw [h0] at hρ3
    simp at hρ3
  have hρ1 : ρ ≠ 1 := fun h => hl (by rw [hσl, h, one_mul])
  have hq : ρ ^ 2 + ρ + 1 = 0 := by
    have : (ρ - 1) * (ρ ^ 2 + ρ + 1) = 0 := by linear_combination hρ3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hρ1)
  have hσq : σ ρ ^ 2 + σ ρ + 1 = 0 := by
    have := congrArg σ hq
    simpa [map_add, map_pow] using this
  have hfac : (σ ρ - ρ) * (σ ρ - ρ ^ 2) = 0 := by
    linear_combination hσq - σ ρ * hq + hρ3
  rcases mul_eq_zero.mp hfac with h | h
  ·
    have hσρ : σ ρ = ρ := sub_eq_zero.mp h
    have hσσl : σ (σ l) = ρ ^ 2 * l := by
      rw [hσl, map_mul, hσρ, hσl]
      ring
    have hl3 : l ^ 3 = 1 := by
      rw [hσσl, hσl] at hn
      linear_combination hn - (l ^ 3) * hρ3
    have hroots : (l - 1) * (l - ρ) * (l - ρ ^ 2) = 0 := by
      linear_combination hl3 - l ^ 2 * hq + l * hq + l * hρ3 - hρ3
    rcases mul_eq_zero.mp hroots with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hl (by rw [sub_eq_zero.mp h'', map_one])
      · exact hl (by rw [sub_eq_zero.mp h'', hσρ])
    · exact hl (by rw [sub_eq_zero.mp h', map_pow, hσρ])
  ·
    have hσρ : σ ρ = ρ ^ 2 := sub_eq_zero.mp h
    have hσσρ : σ (σ ρ) = ρ := by
      rw [hσρ, map_pow, hσρ]
      linear_combination ρ * hρ3
    have hcube := sigma_cube h3 ρ
    rw [hσσρ, hσρ] at hcube
    apply hρ1
    have : ρ * (ρ - 1) = 0 := by linear_combination hcube
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hρ0)

theorem notRatProj_conj (h3 : orderOf σ = 3) {h k : GL (Fin 3) F} {l : F}
    (hk : (k : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hku : (k : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) =
      l • ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1))
    (hl : σ l ≠ l) (hn : l * σ l * σ (σ l) = 1) : NotRatProj σ (h⁻¹ * k * h) := by
  rintro ⟨c, hc0, hc⟩
  set N := ((h⁻¹ * k * h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hN : N = ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * k * h := by
    simp [N, Units.val_mul]
  have hNe : N *ᵥ Pi.single 0 1 = l • Pi.single 0 1 := by
    rw [hN, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hku, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
  have hN00 : N 0 0 = l := by
    have := congrFun hNe 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this
  have hcl : σ (c * l) = c * l := by rw [← hN00]; exact hc 0 0
  have hdetN : N.det = 1 := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, hk, mul_one, ← Matrix.det_mul, coe_inv_mul,
      Matrix.det_one]
  have hcN : IsRatM σ (c • N) := fun i j => by simpa [Matrix.smul_apply] using hc i j
  have hmap : (c • N).map σ = c • N := by
    ext i j
    exact hcN i j
  have hdet : σ ((c • N).det) = (c • N).det := by
    have := RingHom.map_det (σ : F →+* F) (c • N)
    rw [RingHom.mapMatrix_apply] at this
    simp only [RingEquiv.coe_toRingHom] at this
    rw [this]
    congr 1
  rw [Matrix.det_smul, hdetN, mul_one, Fintype.card_fin] at hdet
  have hl3 : σ (l ^ 3) = l ^ 3 := by
    have hc3 : c ^ 3 ≠ 0 := pow_ne_zero 3 hc0
    have e : l ^ 3 = (c * l) ^ 3 / c ^ 3 := by field_simp
    rw [e, map_div₀, map_pow σ (c * l) 3, hcl, hdet]
  exact cube_contra h3 hl hn hl3

theorem conjGL3_toGL (k y : SpecialLinearGroup (Fin 3) F) :
    conjGL3 (Matrix.SpecialLinearGroup.toGL k) y = k * y * k⁻¹ := by
  apply Subtype.ext
  rw [conjGL3_coe, ← map_inv]
  rfl

theorem map_joinH_conj_le {h : GL (Fin 3) F} {k : SpecialLinearGroup (Fin 3) F}
    (hk : k ∈ fixSL3 σ) :
    (joinH σ (h⁻¹ * Matrix.SpecialLinearGroup.toGL k * h)).map (conjGL3 h) ≤ joinH σ h := by
  unfold joinH
  rw [Subgroup.map_sup, Subgroup.map_map, ← conjGL3_mul,
    show h * (h⁻¹ * Matrix.SpecialLinearGroup.toGL k * h) =
      Matrix.SpecialLinearGroup.toGL k * h by group,
    conjGL3_mul, ← Subgroup.map_map]
  refine sup_le le_sup_right ?_
  rintro _ ⟨y, hy, rfl⟩
  rw [conjGL3_toGL]
  have hk' : k ∈ fixSL3 σ ⊔ (fixSL3 σ).map (conjGL3 h) := le_sup_left (a := fixSL3 σ) hk
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk' (le_sup_right (b := (fixSL3 σ).map
    (conjGL3 h)) hy)) (Subgroup.inv_mem _ hk')

theorem top_le_map_of_top_le {J : Subgroup (SpecialLinearGroup (Fin 3) F)} (h : GL (Fin 3) F)
    (hJ : ⊤ ≤ J) : ⊤ ≤ J.map (conjGL3 h) := fun x _ =>
  ⟨conjGL3 h⁻¹ x, hJ (Subgroup.mem_top _), conjGL3_apply_inv h x⟩

theorem top_le_joinH_of_indep [Finite F] (h3 : orderOf σ = 3) {h : GL (Fin 3) F}
    (hind : ∀ b : Fin 3 → F, IsRat σ b →
      b ⬝ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1) = 0 → b = 0) :
    ⊤ ≤ joinH σ h := by
  set u := (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 with hu
  have hP := det_frobMat_ne_zero h3 hind
  obtain ⟨l, hl, hn⟩ := exists_norm_one h3
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hn
  have hdet : (torusMat σ u l).det = 1 := by rw [det_torusMat hP, hn]
  let k : SpecialLinearGroup (Fin 3) F := ⟨torusMat σ u l, hdet⟩
  have hk : k ∈ fixSL3 σ := isRatM_torusMat hP h3 l
  set kGL := Matrix.SpecialLinearGroup.toGL k
  have hkGL : (kGL : Matrix (Fin 3) (Fin 3) F) = torusMat σ u l := rfl
  have hnr : NotRatProj σ (h⁻¹ * kGL * h) :=
    notRatProj_conj h3 (by rw [hkGL]; exact hdet) (by rw [hkGL]; exact torusMat_mulVec hP l) hl hn
  set lu : Fˣ := Units.mk0 l hl0
  set h'' := Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹ * (h⁻¹ * kGL * h)
  have hsc : ∀ v : Fin 3 → F,
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ v = l⁻¹ • v := by
    intro v
    funext i
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal,
      Units.val_inv_eq_inv_val, Units.val_mk0, lu, Pi.smul_apply, smul_eq_mul]
  have hscij : ∀ M : Matrix (Fin 3) (Fin 3) F, ∀ i j,
      (((Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * M) i j = l⁻¹ * M i j := by
    intro M i j
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0, lu]
  have hN : ((h⁻¹ * kGL * h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 =
      l • Pi.single 0 1 := by
    simp only [Units.val_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu, hkGL, torusMat_mulVec hP,
      Matrix.mulVec_smul, hu, Matrix.mulVec_mulVec, coe_inv_mul, Matrix.one_mulVec]
  have hfix : (h'' : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    rw [show (h'' : Matrix (Fin 3) (Fin 3) F) =
        ((Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * ((h⁻¹ * kGL * h : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) from Units.val_mul _ _,
      ← Matrix.mulVec_mulVec, hN, hsc, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hnr'' : NotRatProj σ h'' := by
    rintro ⟨c, hc0, hc⟩
    apply hnr
    refine ⟨c * l⁻¹, mul_ne_zero hc0 (inv_ne_zero hl0), fun i j => ?_⟩
    have := hc i j
    have e : (h'' : Matrix (Fin 3) (Fin 3) F) i j =
        l⁻¹ * ((h⁻¹ * kGL * h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j := by
      rw [show (h'' : Matrix (Fin 3) (Fin 3) F) =
          ((Matrix.GeneralLinearGroup.scalar (Fin 3) lu⁻¹ : GL (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F) * ((h⁻¹ * kGL * h : GL (Fin 3) F) :
              Matrix (Fin 3) (Fin 3) F) from Units.val_mul _ _, hscij]
    rw [e, ← mul_assoc] at this
    exact this
  have htop := top_le_joinH_of_fix (orderOf_prime_of_three h3) hfix hnr''
  rw [joinH_scalar_mul] at htop
  exact (top_le_map_of_top_le h htop).trans (map_joinH_conj_le hk)

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
