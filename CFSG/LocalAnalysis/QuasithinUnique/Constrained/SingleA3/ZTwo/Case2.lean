module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.ZTwo.Normalizer

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin Subgroup ZTwoAux

namespace ZTwoConfig

variable {G : Type} [Group G] [Finite G] {T S U R : Subgroup G} {y x c : G}
  (h : ZTwoConfig T S U R y x c) {z : G} (hd : D8Data R U (conjSubgroup U x) z)
  {e : G} (hes : ∃ s₁ ∈ S, e = x * s₁) (he2 : e ^ 2 = 1)

include h hd hes he2

theorem e_conj_y : e * y * e = z * y := by
  obtain ⟨s₁, hs₁, hs⟩ := hes
  have := h.conj_y_e hd hs₁
  rw [← hs, inv_eq_self_of_sq_eq_one he2] at this
  exact this

theorem e_conj_z : e * z * e = z := by
  obtain ⟨s₁, hs₁, hs⟩ := hes
  have := h.conj_z_e hd hs₁
  rw [← hs, inv_eq_self_of_sq_eq_one he2] at this
  exact this

theorem t_sq : (e * y) * (e * y) = z := by
  have h1 := h.e_conj_y hd hes he2
  have hy : y * y = 1 := by simpa [pow_two] using h.y_sq
  calc e * y * (e * y) = (e * y * e) * y := by group
    _ = z * (y * y) := by rw [h1]; group
    _ = z := by rw [hy, mul_one]

theorem t_inv : (e * y)⁻¹ = z * (e * y) := by
  have h1 := h.t_sq hd hes he2
  have hz : z * z = 1 := by simpa [pow_two] using hd.z_sq
  have h2 : z * (e * y) * (e * y) = 1 := by
    calc z * (e * y) * (e * y) = z * ((e * y) * (e * y)) := by rw [mul_assoc]
      _ = 1 := by rw [h1, hz]
  exact (eq_inv_of_mul_eq_one_left h2).symm

variable (heT : e ∈ T)

include heT

omit hd hes he2 in
theorem t_mem_T : e * y ∈ T := T.mul_mem heT (h.S_le h.y_mem)

theorem mem_K_iff {g : G} :
    g ∈ R ⊔ zpowers (e * y) ↔ g ∈ R ∨ ∃ r ∈ R, g = r * (e * y) := by
  have ht := h.t_mem_T heT
  have hnorm : e * y ∈ normalizer (R : Set G) := h.T_norm_R hd ht
  have hle : zpowers (e * y) ≤ normalizer (R : Set G) := zpowers_le.mpr hnorm
  have hzR : z ∈ R := h.U_le_R hd.z_mem_U
  have hsq : (e * y) ^ (2 : ℤ) = z := by rw [zpow_two]; exact h.t_sq hd hes he2
  rw [sup_comm, A3Dich.mem_sup_iff_of_le_normalizer hle]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · left
      have : (e * y) ^ (2 * n) = z ^ n := by rw [zpow_mul, hsq]
      rw [this]
      exact R.mul_mem (R.zpow_mem hzR n) hb
    · right
      have e1 : (e * y) ^ (2 * n + 1) = z ^ n * (e * y) := by
        rw [zpow_add_one, zpow_mul, hsq]
      have hb' : (e * y) * b * (e * y)⁻¹ ∈ R := (mem_normalizer_iff.mp hnorm b).mp hb
      refine ⟨z ^ n * ((e * y) * b * (e * y)⁻¹), R.mul_mem (R.zpow_mem hzR n) hb', ?_⟩
      rw [e1]
      group
  · rintro (hg | ⟨r, hr, rfl⟩)
    · exact ⟨1, one_mem _, g, hg, by simp⟩
    · refine ⟨e * y, mem_zpowers _, (e * y)⁻¹ * r * (e * y), ?_, by group⟩
      have := (mem_normalizer_iff.mp (inv_mem hnorm) r).mp hr
      simpa using this

theorem y_not_mem_K (heS : e ∉ S) : y ∉ R ⊔ zpowers (e * y) := by
  rw [h.mem_K_iff hd hes he2 heT]
  rintro (hyR | ⟨r, hr, hyr⟩)
  · exact h.y_not_mem_R hyR
  · apply heS
    have h1 : r * e = 1 := by
      have : (r * e) * y = 1 * y := by
        rw [one_mul, mul_assoc]
        exact hyr.symm
      exact mul_right_cancel this
    have h2 : e = r⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact S.inv_mem (h.R_le hr)

omit hd hes he2 in
theorem K_le_T : R ⊔ zpowers (e * y) ≤ T :=
  sup_le (h.R_le.trans h.S_le) (zpowers_le.mpr (h.t_mem_T heT))

omit hes he2 in
theorem T_le_normalizer_K : T ≤ normalizer ((R ⊔ zpowers (e * y) : Subgroup G) : Set G) :=
  le_normalizer_of_commutator_le (h.K_le_T heT)
    ((h.commutator_T_le_R hd).trans le_sup_left)

theorem inv_mul_mem_K {w : G} (hwT : w ∈ T) (hwS : w ∉ S) (hw2 : w ^ 2 = 1) :
    y⁻¹ * w ∈ R ⊔ zpowers (e * y) := by
  obtain ⟨s, hs, hws⟩ := (h.T_decomp hd hwT).resolve_left hwS
  obtain ⟨s₁, hs₁, hes'⟩ := hes
  have hew : e * w ∈ S := by
    rw [hws, hes']
    have e1 : x * s₁ * (x * s) = x ^ 2 * (x⁻¹ * s₁ * x) * s := by group
    rw [e1]
    exact S.mul_mem (S.mul_mem h.x_sq_mem (h.conj_inv_mem hs₁)) hs
  have hes : ∃ s₁ ∈ S, e = x * s₁ := ⟨s₁, hs₁, hes'⟩
  have hee : e * e = 1 := by simpa [pow_two] using he2
  have he_inv : e⁻¹ = e := inv_eq_self_of_sq_eq_one he2
  have hnormR : ∀ r ∈ R, e * r * e ∈ R := by
    intro r hr
    have := (mem_normalizer_iff.mp (h.T_norm_R hd heT) r).mp hr
    rwa [he_inv] at this
  have hy2 : y⁻¹ = y := inv_eq_self_of_sq_eq_one h.y_sq
  have hyc : ∀ r ∈ R, y * r = r * y := fun r hr => (h.y_comm r (h.R_le hr)).symm
  obtain ⟨r, hr, hr' | hr'⟩ := (h.mem_S_iff).mp hew
  ·
    have hw : w = e * r := by
      calc w = e⁻¹ * (e * w) := by group
        _ = e * r := by rw [hr', he_inv]
    have hye : y * e = z * (e * y) := by
      have := h.t_inv hd hes he2
      rwa [mul_inv_rev, he_inv, hy2] at this
    have ht := h.t_mem_T heT
    have hnorm : e * y ∈ normalizer (R : Set G) := h.T_norm_R hd ht
    have hzR : z ∈ R := h.U_le_R hd.z_mem_U
    rw [hy2, hw]
    rw [h.mem_K_iff hd hes he2 heT]
    right
    refine ⟨z * ((e * y) * r * (e * y)⁻¹), R.mul_mem hzR ((mem_normalizer_iff.mp hnorm r).mp hr),
      ?_⟩
    calc y * (e * r) = (y * e) * r := by rw [mul_assoc]
      _ = z * (e * y) * r := by rw [hye]
      _ = z * ((e * y) * r * (e * y)⁻¹) * (e * y) := by group
  ·
    exfalso
    have hw : w = (e * r * e) * (e * y) := by
      calc w = e⁻¹ * (e * w) := by group
        _ = e * (r * y) := by rw [hr', he_inv]
        _ = (e * r * e) * (e * y) := by
          calc e * (r * y) = e * r * (e * e) * y := by rw [hee]; group
            _ = (e * r * e) * (e * y) := by group
    set r' := e * r * e with hr'def
    have hr'R : r' ∈ R := hnormR r hr
    have hsq : (r' * (e * y)) * (r' * (e * y)) = r' * (e * r' * e⁻¹) * z := by
      have h1 := h.t_sq hd hes he2
      calc (r' * (e * y)) * (r' * (e * y))
          = r' * ((e * y) * r' * (e * y)⁻¹) * ((e * y) * (e * y)) := by group
        _ = r' * ((e * y) * r' * (e * y)⁻¹) * z := by rw [h1]
        _ = r' * (e * r' * e⁻¹) * z := by
          congr 2
          calc (e * y) * r' * (e * y)⁻¹ = e * (y * r' * y⁻¹) * e⁻¹ := by group
            _ = e * r' * e⁻¹ := by rw [hyc r' hr'R]; group
    have hβ2 : ∀ g, (MulAut.conj e) ((MulAut.conj e) g) = g := by
      intro g
      simp only [MulAut.conj_apply, he_inv]
      calc e * (e * g * e) * e = (e * e) * g * (e * e) := by group
        _ = g := by rw [hee, one_mul, mul_one]
    obtain ⟨s₂, hs₂, hes2⟩ := hes
    have hU : ∀ u ∈ U, (MulAut.conj e) u ∈ conjSubgroup U x := by
      intro u hu
      have := h.U_conj_e hs₂ hu
      rw [← hes2, he_inv] at this
      simpa [MulAut.conj_apply, he_inv] using this
    have hV : ∀ v ∈ conjSubgroup U x, (MulAut.conj e) v ∈ U := by
      intro v hv
      have := h.U'_conj_e hs₂ hv
      rw [← hes2, he_inv] at this
      simpa [MulAut.conj_apply, he_inv] using this
    have hz : (MulAut.conj e) z = z := by
      have := h.conj_z_e hd hs₂
      rw [← hes2, he_inv] at this
      simpa [MulAut.conj_apply, he_inv] using this
    have hno := hd.no_sq_one (MulAut.conj e) hβ2 hU hV hz hr'R
    apply hno
    rw [MulAut.conj_apply]
    have hw2' : (r' * (e * y)) * (r' * (e * y)) = 1 := by
      rw [hw] at hw2
      simpa [pow_two] using hw2
    rw [← hsq]
    exact hw2'

end ZTwoConfig

end CFSG.QuasithinUnique
