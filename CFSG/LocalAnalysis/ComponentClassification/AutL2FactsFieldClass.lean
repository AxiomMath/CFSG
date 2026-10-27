module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2FieldCent

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup
open CFSG.Glauberman.Dickson (h826_pglMap h826_pglMap_mk h826_pglMap_injective)

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem pgl_eq_one_of_lang {σ : F ≃+* F} (hσσ : ∀ x, σ (σ x) = x) (h2 : (2 : F) ≠ 0)
    (X B : GL (Fin 2) F) (hX : (X : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hB : (B : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hBσ : ∀ i j, σ ((B : Matrix (Fin 2) (Fin 2) F) i j) = (B : Matrix (Fin 2) (Fin 2) F) i j)
    (h : Matrix.ProjGenLinGroup.mk X =
      Matrix.ProjGenLinGroup.mk (B * Matrix.GeneralLinearGroup.map σ.toRingHom X)) :
    Matrix.ProjGenLinGroup.mk B = 1 := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hR : (X : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal (fun _ => (u : F)) =
      (B : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F).map σ := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hu
    simpa [Matrix.GeneralLinearGroup.map] using this
  have hdetσ : ((X : Matrix (Fin 2) (Fin 2) F).map σ).det = 1 := by
    have := RingHom.map_det σ.toRingHom (X : Matrix (Fin 2) (Fin 2) F)
    rw [hX, map_one] at this
    exact this.symm
  have hu2 : (u : F) * u = 1 := by
    have := congrArg Matrix.det hR
    rw [Matrix.det_mul, Matrix.det_mul, hX, hB, hdetσ, Matrix.det_diagonal] at this
    simp only [Fin.prod_univ_two, one_mul] at this
    exact this
  have hσu : σ (u : F) = u := by
    have : ((u : F) - 1) * ((u : F) + 1) = 0 := by linear_combination hu2
    rcases mul_eq_zero.mp this with h1 | h1
    · rw [sub_eq_zero.mp h1, map_one]
    · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_one]
  have hBmap : (B : Matrix (Fin 2) (Fin 2) F).map σ = (B : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    exact hBσ i j
  have hXmap : ((X : Matrix (Fin 2) (Fin 2) F).map σ).map σ = (X : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    exact hσσ _
  have hR' : (X : Matrix (Fin 2) (Fin 2) F).map σ * Matrix.diagonal (fun _ => (u : F)) =
      (B : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) := by
    have hmapmul : ∀ M N : Matrix (Fin 2) (Fin 2) F, (M * N).map σ = M.map σ * N.map σ :=
      fun M N => by
        ext i j
        simp [Matrix.mul_apply, Fin.sum_univ_two]
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M.map σ) hR
    simp only [hmapmul] at this
    rw [hBmap, hXmap, Matrix.diagonal_map (map_zero σ)] at this
    simpa [hσu] using this
  have hDD : Matrix.diagonal (fun _ => (u : F)) * Matrix.diagonal (fun _ => (u : F)) =
      (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext
    exact hu2
  have hBB : (B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
      (X : Matrix (Fin 2) (Fin 2) F) = 1 * (X : Matrix (Fin 2) (Fin 2) F) := by
    calc (B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) *
        (X : Matrix (Fin 2) (Fin 2) F) = (B : Matrix (Fin 2) (Fin 2) F) *
          ((X : Matrix (Fin 2) (Fin 2) F).map σ * Matrix.diagonal (fun _ => (u : F))) := by
          rw [hR', mul_assoc]
      _ = (X : Matrix (Fin 2) (Fin 2) F) * Matrix.diagonal (fun _ => (u : F)) *
          Matrix.diagonal (fun _ => (u : F)) := by
          rw [← mul_assoc, ← hR]
      _ = 1 * (X : Matrix (Fin 2) (Fin 2) F) := by rw [mul_assoc, hDD, mul_one, one_mul]
  have hXunit : IsUnit (X : Matrix (Fin 2) (Fin 2) F) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hX]; exact isUnit_one)
  have hBB1 : (B : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) = 1 :=
    hXunit.mul_right_cancel hBB
  have hadj : (B : Matrix (Fin 2) (Fin 2) F) = Matrix.adjugate (B : Matrix (Fin 2) (Fin 2) F) := by
    calc (B : Matrix (Fin 2) (Fin 2) F) = (B : Matrix (Fin 2) (Fin 2) F)⁻¹ :=
          (Matrix.inv_eq_left_inv hBB1).symm
      _ = _ := by rw [Matrix.inv_def, hB, Ring.inverse_one, one_smul]
  have e01 := congrFun (congrFun hadj 0) 1
  have e10 := congrFun (congrFun hadj 1) 0
  have e00 := congrFun (congrFun hadj 0) 0
  simp [Matrix.adjugate_fin_two] at e01 e10 e00
  have h01 : (B : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h2' : (2 : F) * (B : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination e01
    exact (mul_eq_zero.mp h2').resolve_left h2
  have h10 : (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h2' : (2 : F) * (B : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.mp h2').resolve_left h2
  have hb0 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    rw [Matrix.det_fin_two, h0, h01] at hB
    simp at hB
  rw [← map_one Matrix.ProjGenLinGroup.mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 _ (inv_ne_zero hb0), Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, ← e00, hb0]

theorem exists_lang_iff {σ : F ≃+* F} (hσσ : ∀ x, σ (σ x) = x) {K₀ : Subfield F}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card F = Nat.card K₀ ^ 2)
    (h90 : ∀ c : F, c * σ c = 1 → ∃ y : Fˣ, (y : F) / σ y = c)
    (hodd : IsOddPrimePower (Nat.card F)) (hK₀odd : IsOddPrimePower (Nat.card K₀))
    (h3 : 3 < Nat.card K₀) {y₀ : PSL2 F} (hy₀ : y₀ ∈ fieldCent σ) (hy₀2 : y₀ ^ 2 = 1) :
    (∃ x : PSL2 F, x * (psl2FieldAut F σ x)⁻¹ = y₀) ↔ (y₀ = 1 ∨ y₀ ∉ (psl2Sub K₀).range) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_isOddPrimePower hodd
  constructor
  ·
    rintro ⟨x, hx⟩
    by_cases hr : y₀ ∈ (psl2Sub K₀).range
    · left
      obtain ⟨w, rfl⟩ := hr
      obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨W, rfl⟩ := QuotientGroup.mk_surjective w
      have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL hx
      rw [map_mul, map_inv, psl2FieldAut_toPGL, toPGL_psl2Sub,
        Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
        h826_pglMap_mk, pgl2FieldAut_mk, mul_inv_eq_iff_eq_mul, ← map_mul] at h1
      have hB := pgl_eq_one_of_lang hσσ h2 (Matrix.SpecialLinearGroup.toGL X)
        (Matrix.GeneralLinearGroup.map K₀.subtype (Matrix.SpecialLinearGroup.toGL W))
        (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact X.2)
        (by
          change (K₀.subtype.mapMatrix (W : Matrix (Fin 2) (Fin 2) K₀)).det = 1
          rw [← RingHom.map_det, W.2, map_one])
        (fun i j => (hK₀ _).mp (Subtype.mem _)) h1
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [map_one, toPGL_psl2Sub, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, h826_pglMap_mk,
        hB]
    · exact Or.inr hr
  · rintro (h1 | hr)
    · exact ⟨1, by rw [map_one, inv_one, mul_one, h1]⟩
    have hfix : pgl2FieldAut F σ (Matrix.ProjectiveSpecialLinearGroup.toPGL y₀) =
        Matrix.ProjectiveSpecialLinearGroup.toPGL y₀ := by
      rw [← psl2FieldAut_toPGL]
      exact congrArg _ hy₀
    obtain ⟨z, hz⟩ := mem_range_of_pgl2FieldAut_fixed hK₀ h90 hσσ hfix
    have hinjh := h826_pglMap_injective _ K₀.subtype_injective
    have hz2 : z * z = 1 := by
      apply hinjh
      rw [map_mul, hz, ← map_mul, ← pow_two, hy₀2, map_one, map_one]
    have hz1 : z ≠ 1 := by
      rintro rfl
      apply hr
      refine ⟨1, Matrix.ProjectiveSpecialLinearGroup.toPGL_injective ?_⟩
      rw [toPGL_psl2Sub, map_one, map_one, ← hz, map_one]
    have hzr : z ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K₀)).range := by
      rintro ⟨w, rfl⟩
      apply hr
      refine ⟨w, Matrix.ProjectiveSpecialLinearGroup.toPGL_injective ?_⟩
      rw [toPGL_psl2Sub, hz]
    have : Fintype K₀ := Fintype.ofFinite K₀
    have hchar : ringChar K₀ ≠ 2 := by
      intro h
      apply two_ne_zero_of_isOddPrimePower hK₀odd
      have := ringChar.Nat.cast_ringChar (R := K₀)
      rw [h] at this
      exact_mod_cast this
    obtain ⟨δ, hδ⟩ := FiniteField.exists_nonsquare hchar
    have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
    set Z₁ : GL (Fin 2) K₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -δ; 1, 0]
      (by simp [Matrix.det_fin_two, hδ0]) with hZ₁
    set z₁ : PGL2 K₀ := Matrix.ProjGenLinGroup.mk Z₁ with hz₁
    have hz₁2 : z₁ * z₁ = 1 := by
      rw [hz₁, ← map_mul, ← map_one Matrix.ProjGenLinGroup.mk,
        Matrix.ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨Units.mk0 _ (inv_ne_zero (neg_ne_zero.mpr hδ0)),
        Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
      fin_cases i <;> fin_cases j <;>
        simp [hZ₁, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two, hδ0]
    have hz₁1 : z₁ ≠ 1 := by
      intro h
      rw [hz₁, ← map_one Matrix.ProjGenLinGroup.mk, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
      obtain ⟨u, hu⟩ := h
      have := congrArg (fun g : GL (Fin 2) K₀ => (g : Matrix (Fin 2) (Fin 2) K₀) 1 0) hu
      simp [hZ₁, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two] at this
    have hz₁r : z₁ ∉
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K₀)).range := by
      rw [hz₁, pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply]
      simpa [hZ₁, Matrix.det_fin_two] using hδ
    have hJ₀ := pgl2_commutator_eq_psl2_range_of_card_gt_three K₀ hK₀odd h3
    obtain ⟨c, hc⟩ := isConj_iff.mp (pgl2_outer_involutions_conjugate K₀ hK₀odd h3
      ⟨hz₁1, by rw [pow_two]; exact hz₁2⟩ ⟨hz1, by rw [pow_two]; exact hz2⟩
      (by rw [hJ₀]; exact hz₁r) (by rw [hJ₀]; exact hzr))
    obtain ⟨θ, hθ⟩ := isSquare_of_mem_fixed hcard hodd δ
    have hθ0 : θ ≠ 0 := by
      intro h
      apply hδ0
      apply Subtype.ext
      rw [hθ, h, mul_zero]
      rfl
    have hσθ : σ θ = -θ := by
      have hsq : (σ θ) ^ 2 = θ ^ 2 := by
        rw [← map_pow, pow_two θ, ← hθ]
        exact (hK₀ _).mp δ.2
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exfalso
        apply hδ
        refine ⟨⟨θ, (hK₀ θ).mpr h⟩, Subtype.ext ?_⟩
        rw [hθ]
        rfl
      · exact h
    have hσθi : σ θ⁻¹ = -θ⁻¹ := by rw [map_inv₀, hσθ, inv_neg]
    have hdetX : (!![1, θ; θ⁻¹, -1] : Matrix (Fin 2) (Fin 2) F).det = -2 := by
      rw [Matrix.det_fin_two_of]
      field_simp
      ring
    set X : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, θ; θ⁻¹, -1]
      (by rw [hdetX]; exact neg_ne_zero.mpr h2) with hXdef
    have hXL : Matrix.ProjGenLinGroup.mk X ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, Matrix.GeneralLinearGroup.val_det_apply]
      change IsSquare (!![1, θ; θ⁻¹, -1] : Matrix (Fin 2) (Fin 2) F).det
      rw [hdetX]
      exact isSquare_of_mem_fixed hcard hodd (-2)
    obtain ⟨x₁, hx₁⟩ := hXL
    have hlang₁ : Matrix.ProjectiveSpecialLinearGroup.toPGL x₁ *
        (pgl2FieldAut F σ (Matrix.ProjectiveSpecialLinearGroup.toPGL x₁))⁻¹ =
          h826_pglMap K₀.subtype z₁ := by
      rw [hx₁, pgl2FieldAut_mk, hz₁, h826_pglMap_mk, mul_inv_eq_iff_eq_mul, ← map_mul,
        Matrix.ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨Units.mk0 θ hθ0, Matrix.GeneralLinearGroup.ext fun i j => ?_⟩
      have hδF : ((δ : K₀) : F) = θ * θ := hθ
      fin_cases i <;> fin_cases j <;>
        simp [hXdef, hZ₁, Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.GeneralLinearGroup.map, hσθ, hσθi, hδF, hθ0]
    obtain ⟨c', hc'⟩ := mem_psl2Range_of_pgl2FieldAut_fixed hK₀ h90 hσσ hcard hodd
      (pgl2FieldAut_pglMap hK₀ c)
    have hσc' : psl2FieldAut F σ c' = c' := by
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [psl2FieldAut_toPGL, hc', pgl2FieldAut_pglMap hK₀ c]
    refine ⟨c' * x₁, Matrix.ProjectiveSpecialLinearGroup.toPGL_injective ?_⟩
    rw [map_mul (psl2FieldAut F σ), hσc', mul_inv_rev, map_mul, map_mul, map_mul, map_inv,
      map_inv, psl2FieldAut_toPGL, hc', ← hz, ← hc, map_mul, map_mul, map_inv, ← hlang₁]
    group

theorem autPSL2FieldClass :
    ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → Even f → 16 ∣ p ^ f - 1 →
      Blueprint.LieModel Y .PSL 2 p f → ∀ k : MulAut Y, HarrisLit.IsFieldAutPSL2 k →
        ∀ y ∈ MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y), y ^ 2 = 1 →
          ((∃ g : Y, MulAut.conj g * k * (MulAut.conj g)⁻¹ = MulAut.conj y * k) ↔
            (y = 1 ∨ y ∉ (perfectResidual ↥(MonoidHom.eqLocus k.toMonoidHom
              (MonoidHom.id Y))).map
                (MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y)).subtype)) := by
  intro Y _ _ p f hp hp2 hfe h16 hY k hk y hy hy2
  obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF hfe h16
  have hodd := hH.odd
  have hY4 : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
    obtain ⟨y, hy4, hy2⟩ := exists_psl2_pow_four (F := F) (by have := hH.four_le; omega)
    refine ⟨e.symm y, by rw [← map_pow, hy4, map_one], fun h => hy2 ?_⟩
    rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)
  obtain ⟨b, σ, hσ, hkb⟩ := (isFieldAutPSL2_iff hodd e hY4 k).mp hk
  set E : Y ≃* PSL2 F := e.trans (semilinearAction F b⁻¹) with hEdef
  have hE : autEquiv E k = SemidirectProduct.inr σ := by
    rw [autEquiv_eq_iff, congr_trans_apply, ← semilinearAction_autEquiv e k, hkb, congr_self_eq,
      ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    have := congrArg (fun τ : F ≃+* F => τ z) h1
    simpa using this
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p', n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  have hK₀odd' : Odd (Nat.card K₀) := by
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := isOddPrimePower_of_odd_card _ hK₀odd'
  have hr3 : Nat.card K₀ ≠ 3 := by
    intro h3
    have h9 : p ^ f = 9 := by rw [← hF, hcard, h3]; norm_num
    rw [h9] at h16
    norm_num at h16
  have hr5 : 5 ≤ Nat.card K₀ := by
    obtain ⟨j, hj⟩ := hK₀odd'
    have h1 : 1 < Nat.card K₀ := Finite.one_lt_card
    omega
  have : Group.IsPerfect (PSL2 K₀) := psl2_isPerfect_of_card_gt_three K₀ (by omega)
  set C := MonoidHom.eqLocus k.toMonoidHom (MonoidHom.id Y) with hCdef
  have hmemC : ∀ y : Y, y ∈ C ↔ E y ∈ fieldCent σ := by
    intro y
    change k y = y ↔ psl2FieldAut F σ (E y) = E y
    rw [← semilinearAction_inr, ← hE, semilinearAction_autEquiv_apply, E.injective.eq_iff]
  have hmap : C.map E.toMonoidHom = fieldCent σ := by
    ext z
    rw [Subgroup.mem_map_equiv, hmemC, MulEquiv.apply_symm_apply]
  have hCcard : Nat.card C = Nat.card (PGL2 K₀) := by
    rw [← card_fieldCent_eq hK₀ h90 hσσ hcard hodd, ← hmap,
      Subgroup.card_map_of_injective E.injective]
  let ψ : PSL2 K₀ →* C := (E.symm.toMonoidHom.comp (psl2Sub K₀)).codRestrict C fun g =>
    (hmemC _).mpr (by
      show E (E.symm (psl2Sub K₀ g)) ∈ fieldCent σ
      rw [MulEquiv.apply_symm_apply]
      exact psl2Sub_mem_fieldCent hK₀ g)
  have hψ : Function.Injective ψ := fun a b h =>
    psl2Sub_injective K₀ (E.symm.injective (congrArg Subtype.val h))
  have hPR : perfectResidual C = ψ.range := by
    refine perfectResidual_eq_of_two_mul (Group.IsPerfect.range ψ) ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hCcard, pgl2_card_eq_two_mul hK₀odd]
  have hres : y ∈ (perfectResidual C).map C.subtype ↔ E y ∈ (psl2Sub K₀).range := by
    rw [hPR]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, hw⟩
      refine ⟨w, ?_⟩
      rw [← hw]
      show psl2Sub K₀ w = E (E.symm (psl2Sub K₀ w))
      rw [MulEquiv.apply_symm_apply]
    · rintro ⟨w, hw⟩
      refine ⟨ψ w, ⟨w, rfl⟩, ?_⟩
      show E.symm (psl2Sub K₀ w) = y
      rw [hw, MulEquiv.symm_apply_apply]
  set Φ := autEquiv E with hΦ
  have hconj : ∀ g : Y, MulAut.conj g * k * (MulAut.conj g)⁻¹ = MulAut.conj y * k ↔
      E g * (psl2FieldAut F σ (E g))⁻¹ = E y := by
    intro g
    have hσincl : ∀ w : PSL2 F, (SemidirectProduct.inr σ : PGammaL2 F) * incl F w =
        incl F (psl2FieldAut F σ w) * SemidirectProduct.inr σ := by
      intro w
      have := conj_incl (SemidirectProduct.inr σ) w
      rw [semilinearAction_inr] at this
      rw [← this]
      group
    rw [← Φ.injective.eq_iff, map_mul, map_mul, map_mul, map_inv, autEquiv_conj, autEquiv_conj,
      hE]
    have hlhs : incl F (E g) * SemidirectProduct.inr σ * (incl F (E g))⁻¹ =
        incl F (E g * (psl2FieldAut F σ (E g))⁻¹) * SemidirectProduct.inr σ := by
      rw [map_mul, map_inv, ← map_inv (incl F), mul_assoc, hσincl, map_inv, ← mul_assoc,
        map_inv]
    rw [hlhs, mul_left_inj, (incl_injective F).eq_iff]
  have hEy : E y ∈ fieldCent σ := (hmemC y).mp hy
  have hEy2 : E y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have key := exists_lang_iff hσσ hK₀ hcard h90 hodd hK₀odd (by omega) hEy hEy2
  constructor
  · rintro ⟨g, hg⟩
    have := key.mp ⟨E g, (hconj g).mp hg⟩
    rcases this with h | h
    · left
      exact E.injective (h.trans (map_one E).symm)
    · right
      rwa [hres]
  · intro h
    obtain ⟨x, hx⟩ := key.mpr (by
      rcases h with h | h
      · left
        rw [h, map_one]
      · right
        rwa [← hres])
    refine ⟨E.symm x, (hconj _).mpr ?_⟩
    rw [MulEquiv.apply_symm_apply]
    exact hx

end CFSG.ComponentClassification.AutL2Facts
