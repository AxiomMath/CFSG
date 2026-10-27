module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InOut

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Aut

variable {K : Type} [Field K]

theorem eq_one_of_central_det_one (hK : (2 : K) = 0)
    {Z : GL (Fin 2) K} (hZ : Z ∈ Subgroup.center (GL (Fin 2) K))
    (hdet : Matrix.det (Z : Matrix (Fin 2) (Fin 2) K) = 1) : Z = 1 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hZ
  obtain ⟨l, rfl⟩ := hZ
  have h1 : (l : K) ^ 2 = 1 := by
    have := hdet
    simpa [Matrix.det_fin_two, sq] using this
  have h2 : (l : K) = 1 := by
    have h0 : ((l : K) - 1) ^ 2 = 0 := by linear_combination h1 - (l : K) * hK + hK
    exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  have : l = 1 := Units.ext h2
  rw [this, map_one]

variable [Finite K]

theorem exists_semilinear_of_aut (hK : (2 : K) = 0) (Ψ : SL(2, K) ≃* SL(2, K)) :
    ∃ (σ : K ≃+* K) (G : SL(2, K)), ∀ Y : SL(2, K),
      Ψ Y * G = G * Matrix.SpecialLinearGroup.map σ.toRingHom Y := by
  classical
  let ε := psl2EquivSl2 K hK
  have hε : ∀ Y : SL(2, K), ε (QuotientGroup.mk' (Subgroup.center SL(2, K)) Y) = Y :=
    psl2EquivSl2_mk K hK
  have hε' : ∀ Y : SL(2, K), ε.symm Y = QuotientGroup.mk' (Subgroup.center SL(2, K)) Y :=
    fun Y => ε.symm_apply_eq.2 (hε Y).symm
  let Θ : MulAut (PSL2 K) := (ε.trans Ψ).trans ε.symm
  obtain ⟨x, hx⟩ := semilinearAction_surjective K Θ
  have hxx : semilinearAction K x = pglAction K x.left * psl2FieldAut K x.right := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul, semilinearAction_inl, semilinearAction_inr]
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  have hΘ : ∀ Y : SL(2, K), Θ (QuotientGroup.mk' (Subgroup.center SL(2, K)) Y) =
      QuotientGroup.mk' (Subgroup.center SL(2, K)) (Ψ Y) := by
    intro Y
    simp only [Θ, MulEquiv.trans_apply, hε, hε']
  have h2 : ∀ Y : SL(2, K), Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL (Ψ Y)) =
      Matrix.ProjGenLinGroup.mk (G * Matrix.GeneralLinearGroup.map x.right.toRingHom
        (Matrix.SpecialLinearGroup.toGL Y) * G⁻¹) := by
    intro Y
    have h := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL (hΘ Y)
    rw [← hx, hxx, MulAut.mul_apply, toPGL_pglAction, psl2FieldAut_toPGL] at h
    have e0 : ∀ Z : SL(2, K), Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk' (Subgroup.center SL(2, K)) Z) =
        Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Z) :=
      fun Z => Matrix.ProjectiveSpecialLinearGroup.toPGL_mk Z
    rw [e0, e0] at h
    have e1 : (pgl2FieldAut K) x.right (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Y)) =
        Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map x.right.toRingHom
          (Matrix.SpecialLinearGroup.toGL Y)) := pgl2RingEquiv_mk x.right _
    rw [e1, ← hG] at h
    rw [← h, map_mul, map_mul, map_inv]
  have hdet : ∀ g : GL (Fin 2) K, Matrix.det (g : Matrix (Fin 2) (Fin 2) K) =
      ((Matrix.GeneralLinearGroup.det g : Kˣ) : K) := fun g => rfl
  have h3 : ∀ Y : SL(2, K), (Matrix.SpecialLinearGroup.toGL (Ψ Y)) * G =
      G * Matrix.GeneralLinearGroup.map x.right.toRingHom (Matrix.SpecialLinearGroup.toGL Y) := by
    intro Y
    have h4 : ((Matrix.SpecialLinearGroup.toGL (Ψ Y))⁻¹ *
        (G * Matrix.GeneralLinearGroup.map x.right.toRingHom (Matrix.SpecialLinearGroup.toGL Y) *
          G⁻¹) : GL (Fin 2) K) ∈ Subgroup.center (GL (Fin 2) K) := by
      have := QuotientGroup.eq.1 (h2 Y)
      simpa using this
    have hΨ : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL (Ψ Y)) = 1 :=
      Units.ext (by rw [← hdet]; exact (Ψ Y).det_coe)
    have hY : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map x.right.toRingHom
        (Matrix.SpecialLinearGroup.toGL Y)) = 1 := by
      apply Units.ext
      show Matrix.det ((Matrix.GeneralLinearGroup.map x.right.toRingHom
        (Matrix.SpecialLinearGroup.toGL Y) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
      have : ((Matrix.GeneralLinearGroup.map x.right.toRingHom
          (Matrix.SpecialLinearGroup.toGL Y) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          (Y : Matrix (Fin 2) (Fin 2) K).map x.right := rfl
      have h1 : ((Y : Matrix (Fin 2) (Fin 2) K).map x.right).det =
          x.right.toRingHom ((Y : Matrix (Fin 2) (Fin 2) K).det) :=
        (RingHom.map_det x.right.toRingHom (Y : Matrix (Fin 2) (Fin 2) K)).symm
      rw [this, h1, Y.det_coe]
      simp
    have hZdet : Matrix.det (((Matrix.SpecialLinearGroup.toGL (Ψ Y))⁻¹ *
        (G * Matrix.GeneralLinearGroup.map x.right.toRingHom (Matrix.SpecialLinearGroup.toGL Y) *
          G⁻¹) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [hdet]
      simp only [map_mul, map_inv, hΨ, hY]
      simp
    have h5 := eq_one_of_central_det_one hK h4 hZdet
    rw [inv_mul_eq_one] at h5
    calc Matrix.SpecialLinearGroup.toGL (Ψ Y) * G =
        (G * Matrix.GeneralLinearGroup.map x.right.toRingHom (Matrix.SpecialLinearGroup.toGL Y) *
          G⁻¹) * G := by rw [h5]
      _ = G * Matrix.GeneralLinearGroup.map x.right.toRingHom (Matrix.SpecialLinearGroup.toGL Y) := by
        group
  have hcp : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast hK)
  have hrc : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two hrc (Matrix.det (G : Matrix (Fin 2) (Fin 2) K))
  have hdetG : Matrix.det (G : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    rw [hdet]; exact (Matrix.GeneralLinearGroup.det G).ne_zero
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hdetG (by rw [hl]; simp)
  let Gs : SL(2, K) := ⟨l⁻¹ • (G : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_smul, Fintype.card_fin, hl]
    field_simp⟩
  refine ⟨x.right, Gs, fun Y => ?_⟩
  apply Subtype.ext
  have h6 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) (h3 Y)
  simp only [Units.val_mul] at h6
  change ((Ψ Y : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (l⁻¹ • (G : Matrix (Fin 2) (Fin 2) K)) =
    (l⁻¹ • (G : Matrix (Fin 2) (Fin 2) K)) * (Y : Matrix (Fin 2) (Fin 2) K).map x.right
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact congrArg (fun M => l⁻¹ • M) h6

end Aut

end CFSG.QuasithinUnique.Lin2
