module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_isotropic_not_orthogonal
    {p f : ℕ} {E : Type*} [Field E] (hE : UnitaryFieldData p f E)
    {M : Type*} [AddCommGroup M] [Module E M] [FiniteDimensional E M]
    {H : M →ₛₗ[hE.bar] M →ₗ[E] E} (hsymm : H.IsSymm) (hsep : H.SeparatingLeft)
    (hdim : 2 ≤ Module.finrank E M) {w : M} (hw : w ≠ 0) :
    ∃ u : M, H u u = 0 ∧ H u w ≠ 0 := by
  obtain ⟨e, he⟩ := hE.exists_orthonormal_basis hsymm hsep
  obtain ⟨i, hi⟩ : ∃ i, H (e i) w ≠ 0 := by
    by_contra! hz
    apply hw
    apply hsep w
    intro x
    have hx : H x w = 0 := by
      calc H x w = H (∑ k, e.repr x k • e k) w := by rw [e.sum_repr x]
        _ = 0 := by simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, hz,
          smul_zero, Finset.sum_const_zero]
    rw [← hsymm.eq x w, hx, map_zero]
  obtain ⟨j, hij⟩ : ∃ j, j ≠ i := by
    by_contra! hj
    have : Fintype.card (Fin (Module.finrank E M)) ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun a b => (hj a).trans (hj b).symm
    simp at this
    omega
  obtain ⟨ζ, hζn, hζ1⟩ : ∃ ζ : E, hE.norm ζ = 1 ∧ ζ ≠ 1 := by
    obtain ⟨c, hc⟩ := hE.exists_bar_ne
    have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
    refine ⟨hE.bar c / c, ?_, ?_⟩
    · have := hE.norm_div_bar (r := hE.bar c) ((hE.bar_eq_zero_iff).not.mpr hc0)
      rwa [hE.bar_bar] at this
    · intro h1
      exact hc ((div_eq_one_iff_eq hc0).mp h1)
  obtain ⟨y₀, hy₀⟩ : ∃ y : E, hE.norm y = -1 := by
    have hfix : (-1 : E) ∈ hE.fixedField := by
      rw [UnitaryFieldData.mem_fixedField, map_neg, map_one]
    obtain ⟨y, hy⟩ := hE.normHom_surjective ⟨-1, hfix⟩
    exact ⟨y, by simpa using congrArg Subtype.val hy⟩
  have hy₀0 : y₀ ≠ 0 := by
    rintro rfl
    simp [UnitaryFieldData.norm] at hy₀
  have key : ∀ y : E, hE.norm y = -1 →
      H (e i + y • e j) (e i + y • e j) = 0 ∧
        H (e i + y • e j) w = H (e i) w + hE.bar y * H (e j) w := by
    intro y hy
    refine ⟨?_, by simp [map_add, map_smulₛₗ]⟩
    have h1 : H (e i) (e i) = 1 := by simp [he]
    have h2 : H (e j) (e j) = 1 := by simp [he]
    have h3 : H (e i) (e j) = 0 := by simp [he, hij.symm]
    have h4 : H (e j) (e i) = 0 := by simp [he, hij]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
      h2, h3, h4]
    have : hE.bar y * y = -1 := by rw [mul_comm]; exact hy
    linear_combination this
  by_contra! hcon
  have hb : ∀ y : E, hE.norm y = -1 → H (e i) w + hE.bar y * H (e j) w = 0 := by
    intro y hy
    obtain ⟨hu, hw'⟩ := key y hy
    rw [← hw']
    exact hcon _ hu
  have hζ' : hE.norm (y₀ * ζ) = -1 := by
    simp only [UnitaryFieldData.norm, map_mul] at hζn hy₀ ⊢
    linear_combination (y₀ * hE.bar y₀) * hζn + hy₀
  have h1 := hb y₀ hy₀
  have h2 := hb _ hζ'
  rw [map_mul] at h2
  have hb0 : H (e j) w ≠ 0 := by
    intro h0
    rw [h0, mul_zero, add_zero] at h1
    exact hi h1
  have hby : hE.bar y₀ ≠ 0 := (hE.bar_eq_zero_iff).not.mpr hy₀0
  have hbz : hE.bar ζ = 1 := by
    have : hE.bar y₀ * H (e j) w * (hE.bar ζ - 1) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hby hb0)
    · exact sub_eq_zero.mp h
  apply hζ1
  rw [← hE.bar_bar ζ, hbz, map_one]

end CFSG.HardMathSupport.Curtis.UnitaryLevi
