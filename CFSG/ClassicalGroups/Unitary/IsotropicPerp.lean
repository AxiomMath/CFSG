module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

private lemma exists_iso_of_herm_ne_zero (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {e v : Fin n → K} (he : herm σ e e = 0) (hev : herm σ e v ≠ 0) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_isotropize hσ he (y := (herm σ e v)⁻¹ • v)
    (by rw [herm_smul_right, inv_mul_cancel₀ hev])
  set f := (herm σ e v)⁻¹ • v + c • e with hf
  have hef : herm σ e f = 1 := by
    rw [hf]
    simp only [herm_add_right, herm_smul_right, he, mul_zero, add_zero,
      inv_mul_cancel₀ hev]
  have hff : herm σ f f = 0 := by rw [hf]; exact hc
  obtain ⟨z, hzz, hez, hfz⟩ := exists_norm_one_perp_pair hσ hn he hff hef
  obtain ⟨ν, hν⟩ := hσ.exists_norm (d := -(c + σ c)) (by
    rw [map_neg, map_add, hσ.invol, add_comm])
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hσ.invol, hef, map_one]
  have hze : herm σ z e = 0 := by rw [herm_conj σ hσ.invol, hez, map_zero]
  have hzf : herm σ z f = 0 := by rw [herm_conj σ hσ.invol, hfz, map_zero]
  have hae : herm σ (σ c • e + f + ν • z) e = 1 := by
    simp only [herm_add_left, herm_smul_left, he, hfe, hze, mul_zero, zero_mul, add_zero,
      zero_add]
  have haf : herm σ (σ c • e + f + ν • z) f = c := by
    simp only [herm_add_left, herm_smul_left, hef, hff, hzf, hσ.invol, mul_one, mul_zero,
      zero_mul, add_zero, zero_add]
  have haz : herm σ (σ c • e + f + ν • z) z = σ ν := by
    simp only [herm_add_left, herm_smul_left, hez, hfz, hzz, mul_one, mul_zero, zero_mul,
      add_zero, zero_add]
  have haa : herm σ (σ c • e + f + ν • z) (σ c • e + f + ν • z) = 0 := by
    simp only [herm_add_right, herm_smul_right, hae, haf, haz, mul_one]
    rw [mul_comm ν (σ ν), hν]
    ring
  have hveq : v = (herm σ e v) • f - (herm σ e v * c) • e := by
    rw [hf, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hev, one_smul]
    abel
  refine ⟨σ c • e + f + ν • z, haa, ?_, ?_⟩
  · rw [hveq, herm_sub_right, herm_smul_right, herm_smul_right, hae, haf]
    ring
  · rw [hae]
    exact one_ne_zero

private lemma exists_iso_of_herm_eq_zero_of_isotropic (hσ : IsUnitaryInvolution σ)
    {e v : Fin n → K} (he : herm σ e e = 0) (hvv : herm σ v v = 0)
    (hev : herm σ e v = 0) (hv0 : v ≠ 0) (hev' : ∀ c : K, e ≠ c • v) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  obtain ⟨d, hd, hvd, hed⟩ := exists_iso_perp hσ hv0 hvv he
    (herm_eq_zero_comm σ hσ.invol hev) hev'
  have hde : herm σ d e ≠ 0 := fun h =>
    hed (by rw [herm_conj σ hσ.invol d e, h, map_zero])
  exact ⟨d, hd, herm_eq_zero_comm σ hσ.invol hvd, hde⟩

private lemma exists_iso_of_herm_eq_zero_of_anisotropic (hσ : IsUnitaryInvolution σ)
    {e v : Fin n → K} (he : herm σ e e = 0) (he0 : e ≠ 0)
    (hev : herm σ e v = 0) (hvv : herm σ v v ≠ 0) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hvv
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hve : herm σ v e = 0 := herm_eq_zero_comm σ hσ.invol hev
  have hce : herm σ (c • v) e = 0 := by rw [herm_smul_left, hve, mul_zero]
  obtain ⟨w, hcw, hww, hew⟩ := exists_partner_perp hσ hc he0 he hce
  have hvw : herm σ v w = 0 := by
    have h := hcw
    rw [herm_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left ((map_ne_zero σ).mpr hc0)
  refine ⟨w, hww, herm_eq_zero_comm σ hσ.invol hvw, ?_⟩
  rw [herm_conj σ hσ.invol, hew, map_one]
  exact one_ne_zero

theorem exists_isotropic_herm_eq_zero_herm_ne_zero (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    {e v : Fin n → K} (he : herm σ e e = 0) (he0 : e ≠ 0) (hv : ∀ c : K, v ≠ c • e) :
    ∃ a : Fin n → K, herm σ a a = 0 ∧ herm σ a v = 0 ∧ herm σ a e ≠ 0 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv 0 (by simp)
  have hev' : ∀ c : K, e ≠ c • v := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact he0 (by simpa using hc)
    exact hv c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  by_cases hev : herm σ e v = 0
  · by_cases hvv : herm σ v v = 0
    · exact exists_iso_of_herm_eq_zero_of_isotropic hσ he hvv hev hv0 hev'
    · exact exists_iso_of_herm_eq_zero_of_anisotropic hσ he he0 hev hvv
  · exact exists_iso_of_herm_ne_zero hσ hn he hev

end CFSG.ClassicalGroups.Unitary
