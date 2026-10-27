module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Abs1

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open scoped commutatorElement Pointwise

section Alg2

variable {K : Type} [Group K]

theorem conj_word {w₁ w₂ c₁ c₂ d₁ d₂ : K} (h1 : w₁ * c₁ * w₁⁻¹ = d₁) (h2 : w₂ * c₂ * w₂⁻¹ = d₂)
    (hw2c1 : w₂ * c₁ = c₁ * w₂) (hw1d2 : w₁ * d₂ = d₂ * w₁) :
    (w₁ * w₂) * (c₁ * c₂) * (w₁ * w₂)⁻¹ = d₁ * d₂ := by
  have e1 : w₂ * c₁ * w₂⁻¹ = c₁ := by rw [hw2c1]; group
  calc (w₁ * w₂) * (c₁ * c₂) * (w₁ * w₂)⁻¹
      = w₁ * ((w₂ * c₁ * w₂⁻¹) * (w₂ * c₂ * w₂⁻¹)) * w₁⁻¹ := by group
    _ = w₁ * (c₁ * d₂) * w₁⁻¹ := by rw [e1, h2]
    _ = (w₁ * c₁ * w₁⁻¹) * (w₁ * d₂ * w₁⁻¹) := by group
    _ = d₁ * d₂ := by rw [h1, hw1d2]; group

theorem abs_two {c₁ c₂ x₁ x₂ : K} (hx₁ : x₁ * x₁ = 1) (hx₂ : x₂ * x₂ = 1)
    (hxc₁ : x₁ * c₁ * x₁ = c₁⁻¹) (hxc₂ : x₂ * c₂ * x₂ = c₂⁻¹) (hc₁ : c₁ ^ 3 = 1) (hc₂ : c₂ ^ 3 = 1)
    (h12 : c₁ * c₂ = c₂ * c₁) (hx1c2 : x₁ * c₂ = c₂ * x₁) (hx2c1 : x₂ * c₁ = c₁ * x₂)
    (hne₁ : c₁ ≠ 1) (hne₂ : c₂ ≠ 1) {w₁ w₂ : K}
    (hw₁ : ∃ k : ℤ, w₁ = c₁ ^ k ∨ w₁ = c₁ ^ k * x₁)
    (hw₂ : ∃ k : ℤ, w₂ = c₂ ^ k ∨ w₂ = c₂ ^ k * x₂)
    (h2 : (w₁ * w₂) * (w₁ * w₂) = 1) (hcomm : ⁅w₁ * w₂, c₁ * c₂⁆ = 1) : w₁ * w₂ = 1 := by
  have hx1i : x₁⁻¹ = x₁ := inv_eq_of_mul_eq_one_right hx₁
  have hx2i : x₂⁻¹ = x₂ := inv_eq_of_mul_eq_one_right hx₂
  have hcc : Commute c₁ c₂ := h12
  have hc12k : ∀ k : ℤ, c₂ ^ k * c₁ = c₁ * c₂ ^ k := fun k => ((hcc.zpow_right k).eq).symm
  have hc21k : ∀ k : ℤ, c₁ ^ k * c₂ = c₂ * c₁ ^ k := fun k => ((hcc.zpow_left k).eq)
  have hcx₁ : x₁ * c₁ * x₁⁻¹ = c₁⁻¹ := by rw [hx1i]; exact hxc₁
  have hcx₂ : x₂ * c₂ * x₂⁻¹ = c₂⁻¹ := by rw [hx2i]; exact hxc₂
  have hw2c1 : w₂ * c₁ = c₁ * w₂ := by
    obtain ⟨k, rfl | rfl⟩ := hw₂
    · exact hc12k k
    · calc c₂ ^ k * x₂ * c₁ = c₂ ^ k * (x₂ * c₁) := by group
        _ = c₂ ^ k * (c₁ * x₂) := by rw [hx2c1]
        _ = (c₂ ^ k * c₁) * x₂ := by group
        _ = (c₁ * c₂ ^ k) * x₂ := by rw [hc12k k]
        _ = c₁ * (c₂ ^ k * x₂) := by group
  have hw1c2 : w₁ * c₂ = c₂ * w₁ := by
    obtain ⟨k, rfl | rfl⟩ := hw₁
    · exact hc21k k
    · calc c₁ ^ k * x₁ * c₂ = c₁ ^ k * (x₁ * c₂) := by group
        _ = c₁ ^ k * (c₂ * x₁) := by rw [hx1c2]
        _ = (c₁ ^ k * c₂) * x₁ := by group
        _ = (c₂ * c₁ ^ k) * x₁ := by rw [hc21k k]
        _ = c₂ * (c₁ ^ k * x₁) := by group
  have hw1c2' : w₁ * c₂⁻¹ = c₂⁻¹ * w₁ := by
    have : Commute w₁ c₂ := hw1c2
    exact this.inv_right.eq
  have hθ : (w₁ * w₂) * (c₁ * c₂) * (w₁ * w₂)⁻¹ = c₁ * c₂ := by
    have := (commutatorElement_eq_one_iff_mul_comm.1 hcomm)
    calc (w₁ * w₂) * (c₁ * c₂) * (w₁ * w₂)⁻¹ = ((c₁ * c₂) * (w₁ * w₂)) * (w₁ * w₂)⁻¹ := by
          rw [this]
      _ = c₁ * c₂ := by group
  have hcube : (c₁ * c₂) ^ 3 = 1 := by rw [hcc.mul_pow, hc₁, hc₂, one_mul]
  have hsqne : ∀ {c : K}, c ^ 3 = 1 → c ≠ 1 → c⁻¹ = c → False := fun {c} hc3 hc1 h =>
    hc1 (eq_one_of_mul_self_of_pow_three (by
      calc c * c = c⁻¹ * c := by rw [h]
        _ = 1 := by group) hc3)
  have hpow₁ : ∀ k : ℤ, (c₁ ^ k) * c₁ * (c₁ ^ k)⁻¹ = c₁ := fun k => by group
  have hpow₂ : ∀ k : ℤ, (c₂ ^ k) * c₂ * (c₂ ^ k)⁻¹ = c₂ := fun k => by group
  have hpx₁ : ∀ k : ℤ, (c₁ ^ k * x₁) * c₁ * (c₁ ^ k * x₁)⁻¹ = c₁⁻¹ := fun k => by
    calc (c₁ ^ k * x₁) * c₁ * (c₁ ^ k * x₁)⁻¹ = c₁ ^ k * (x₁ * c₁ * x₁⁻¹) * (c₁ ^ k)⁻¹ := by group
      _ = c₁ ^ k * c₁⁻¹ * (c₁ ^ k)⁻¹ := by rw [hcx₁]
      _ = c₁⁻¹ := by group
  have hpx₂ : ∀ k : ℤ, (c₂ ^ k * x₂) * c₂ * (c₂ ^ k * x₂)⁻¹ = c₂⁻¹ := fun k => by
    calc (c₂ ^ k * x₂) * c₂ * (c₂ ^ k * x₂)⁻¹ = c₂ ^ k * (x₂ * c₂ * x₂⁻¹) * (c₂ ^ k)⁻¹ := by group
      _ = c₂ ^ k * c₂⁻¹ * (c₂ ^ k)⁻¹ := by rw [hcx₂]
      _ = c₂⁻¹ := by group
  obtain ⟨k₁, hk₁⟩ := hw₁
  obtain ⟨k₂, hk₂⟩ := hw₂
  rcases hk₁ with hk₁ | hk₁ <;> rcases hk₂ with hk₂ | hk₂
  ·
    subst hk₁ hk₂
    have hcm : Commute (c₁ ^ k₁) (c₂ ^ k₂) := (hcc.zpow_left k₁).zpow_right k₂
    have h3 : (c₁ ^ k₁ * c₂ ^ k₂) ^ 3 = 1 := by
      rw [hcm.mul_pow, zpow_cube_eq_one hc₁, zpow_cube_eq_one hc₂, one_mul]
    exact eq_one_of_mul_self_of_pow_three h2 h3
  · exfalso
    have := conj_word (d₁ := c₁) (d₂ := c₂⁻¹) (by rw [hk₁]; exact hpow₁ k₁)
      (by rw [hk₂]; exact hpx₂ k₂) hw2c1 hw1c2'
    rw [hθ] at this
    have h' : c₂⁻¹ = c₂ := mul_left_cancel this.symm
    exact hsqne hc₂ hne₂ h'
  · exfalso
    have := conj_word (d₁ := c₁⁻¹) (d₂ := c₂) (by rw [hk₁]; exact hpx₁ k₁)
      (by rw [hk₂]; exact hpow₂ k₂) hw2c1 hw1c2
    rw [hθ] at this
    have h' : c₁⁻¹ = c₁ := mul_right_cancel this.symm
    exact hsqne hc₁ hne₁ h'
  · exfalso
    have := conj_word (d₁ := c₁⁻¹) (d₂ := c₂⁻¹) (by rw [hk₁]; exact hpx₁ k₁)
      (by rw [hk₂]; exact hpx₂ k₂) hw2c1 hw1c2'
    rw [hθ] at this
    have hinv : (c₁ * c₂)⁻¹ = c₁ * c₂ := by
      calc (c₁ * c₂)⁻¹ = c₂⁻¹ * c₁⁻¹ := mul_inv_rev _ _
        _ = c₁⁻¹ * c₂⁻¹ := ((Commute.inv_inv hcc).eq).symm
        _ = c₁ * c₂ := this.symm
    have h5 : (c₁ * c₂) * (c₁ * c₂) = 1 := by
      have h := mul_inv_cancel (c₁ * c₂)
      rwa [hinv] at h
    have h1 : c₁ * c₂ = 1 := eq_one_of_mul_self_of_pow_three h5 hcube
    have hc2 : c₂ = c₁⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h6 : x₁ * c₂ * x₁ = c₂ := by
      calc x₁ * c₂ * x₁ = c₂ * x₁ * x₁ := by rw [hx1c2]
        _ = c₂ := by rw [mul_assoc, hx₁, mul_one]
    rw [hc2] at h6
    have h7 : x₁ * c₁⁻¹ * x₁ = c₁ := by
      calc x₁ * c₁⁻¹ * x₁ = (x₁ * c₁ * x₁)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, hx1i]; group
        _ = c₁ := by rw [hxc₁, inv_inv]
    exact hsqne hc₁ hne₁ ((h7.symm.trans h6).symm)

end Alg2

section Two

variable {H : Type} [Group H]

theorem hasInvolMod_c_two_left {x₁ y₁ x₂ y₂ : H} (h11 : x₁ * x₂ = x₂ * x₁) (h21 : y₁ * x₂ = x₂ * y₁)
    (hx₂ : x₂ * x₂ = 1) (hy₂ : y₂ * y₂ = 1) (h₂3 : (x₂ * y₂) ^ 3 = 1) (h₂1 : x₂ * y₂ ≠ 1) :
    HasInvolMod H (x₁ * y₁) := by
  refine hasInvolMod_of_commute ?_ hx₂ hy₂ h₂3 h₂1
  calc x₁ * y₁ * x₂ = x₁ * (y₁ * x₂) := by group
    _ = x₁ * (x₂ * y₁) := by rw [h21]
    _ = x₁ * x₂ * y₁ := by group
    _ = x₂ * x₁ * y₁ := by rw [h11]
    _ = x₂ * (x₁ * y₁) := by group

theorem not_hasInvolMod_c_two {x₁ y₁ x₂ y₂ : H}
    (hgen : (⊤ : Subgroup H) ≤
      CFSG.pCore 2 H ⊔ (Subgroup.closure {x₁, y₁} ⊔ Subgroup.closure {x₂, y₂}))
    (h11 : x₁ * x₂ = x₂ * x₁) (h12 : x₁ * y₂ = y₂ * x₁) (h21 : y₁ * x₂ = x₂ * y₁)
    (h22 : y₁ * y₂ = y₂ * y₁)
    (hx₁ : x₁ * x₁ = 1) (hy₁ : y₁ * y₁ = 1) (h₁3 : (x₁ * y₁) ^ 3 = 1) (h₁1 : x₁ * y₁ ≠ 1)
    (hx₂ : x₂ * x₂ = 1) (hy₂ : y₂ * y₂ = 1) (h₂3 : (x₂ * y₂) ^ 3 = 1) (h₂1 : x₂ * y₂ ≠ 1) :
    ¬ HasInvolMod H ((x₁ * y₁) * (x₂ * y₂)) := by
  rintro ⟨u, huO, hu2, hcomm⟩
  haveI : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
  set O : Subgroup H := CFSG.pCore 2 H with hO
  set cl₁ : Subgroup H := Subgroup.closure {x₁, y₁} with hcl₁
  set cl₂ : Subgroup H := Subgroup.closure {x₂, y₂} with hcl₂
  have hc12 : ∀ w ∈ cl₁, w * x₂ = x₂ * w ∧ w * y₂ = y₂ * w := fun w hw =>
    ⟨(commute_of_mem_closure_pair h11.symm h21.symm hw).symm,
      (commute_of_mem_closure_pair h12.symm h22.symm hw).symm⟩
  have hN : cl₁ ≤ Subgroup.normalizer (cl₂ : Set H) := fun w hw =>
    mem_normalizer_closure_pair (hc12 w hw).1 (hc12 w hw).2
  have hu : u ∈ (↑(O ⊔ (cl₁ ⊔ cl₂)) : Set H) := hgen (Subgroup.mem_top u)
  rw [Subgroup.normal_mul, Subgroup.coe_mul_of_left_le_normalizer_right cl₁ cl₂ hN] at hu
  obtain ⟨r, hr, v, hv, rfl⟩ := hu
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hv
  obtain ⟨k₁, hk₁⟩ := mem_closure_pair_cases hx₁ hy₁ hw₁
  obtain ⟨k₂, hk₂⟩ := mem_closure_pair_cases hx₂ hy₂ hw₂
  set q : H →* H ⧸ O := QuotientGroup.mk' O with hq
  have hq1 : ∀ g, q g = 1 ↔ g ∈ O := fun g => QuotientGroup.eq_one_iff g
  have hqr : q r = 1 := (hq1 r).2 hr
  have hu2' : (q w₁ * q w₂) * (q w₁ * q w₂) = 1 := by
    have h := (hq1 _).2 hu2
    rw [map_mul q (r * (w₁ * w₂)) (r * (w₁ * w₂)), map_mul q r (w₁ * w₂), hqr, one_mul,
      map_mul q w₁ w₂] at h
    exact h
  have hcomm' : ⁅q w₁ * q w₂, q (x₁ * y₁) * q (x₂ * y₂)⁆ = 1 := by
    have h := (hq1 _).2 hcomm
    rw [map_commutatorElement, map_mul q r (w₁ * w₂), hqr, one_mul, map_mul q w₁ w₂,
      map_mul q (x₁ * y₁) (x₂ * y₂)] at h
    exact h
  have e1 : Commute x₁ (x₂ * y₂) :=
    (show Commute x₁ x₂ from h11).mul_right (show Commute x₁ y₂ from h12)
  have e2 : Commute y₁ (x₂ * y₂) :=
    (show Commute y₁ x₂ from h21).mul_right (show Commute y₁ y₂ from h22)
  have e3 : Commute x₂ (x₁ * y₁) :=
    (show Commute x₂ x₁ from h11.symm).mul_right (show Commute x₂ y₁ from h21.symm)
  have hcc : (x₁ * y₁) * (x₂ * y₂) = (x₂ * y₂) * (x₁ * y₁) := (e1.mul_left e2).eq
  have hq12 : q (x₁ * y₁) * q (x₂ * y₂) = q (x₂ * y₂) * q (x₁ * y₁) := by
    rw [← map_mul, ← map_mul, hcc]
  have hq1c2 : q x₁ * q (x₂ * y₂) = q (x₂ * y₂) * q x₁ := by
    rw [← map_mul, ← map_mul, e1.eq]
  have hq2c1 : q x₂ * q (x₁ * y₁) = q (x₁ * y₁) * q x₂ := by
    rw [← map_mul, ← map_mul, e3.eq]
  have hqx₁ : q x₁ * q x₁ = 1 := by rw [← map_mul, hx₁, map_one]
  have hqx₂ : q x₂ * q x₂ = 1 := by rw [← map_mul, hx₂, map_one]
  have hqxc₁ : q x₁ * q (x₁ * y₁) * q x₁ = (q (x₁ * y₁))⁻¹ := by
    rw [← map_mul, ← map_mul, ← map_inv, conj_c_eq_inv' hx₁ hy₁]
  have hqxc₂ : q x₂ * q (x₂ * y₂) * q x₂ = (q (x₂ * y₂))⁻¹ := by
    rw [← map_mul, ← map_mul, ← map_inv, conj_c_eq_inv' hx₂ hy₂]
  have hqc₁ : (q (x₁ * y₁)) ^ 3 = 1 := by rw [← map_pow, h₁3, map_one]
  have hqc₂ : (q (x₂ * y₂)) ^ 3 = 1 := by rw [← map_pow, h₂3, map_one]
  have hne₁ : q (x₁ * y₁) ≠ 1 := fun h =>
    not_mem_pCore_two_of_pow_three h₁3 h₁1 ((hq1 _).1 h)
  have hne₂ : q (x₂ * y₂) ≠ 1 := fun h =>
    not_mem_pCore_two_of_pow_three h₂3 h₂1 ((hq1 _).1 h)
  have hqw₁ : ∃ k : ℤ, q w₁ = (q (x₁ * y₁)) ^ k ∨ q w₁ = (q (x₁ * y₁)) ^ k * q x₁ := by
    refine ⟨k₁, ?_⟩
    rcases hk₁ with h | h
    · left; rw [h, map_zpow]
    · right; rw [h, map_mul, map_zpow]
  have hqw₂ : ∃ k : ℤ, q w₂ = (q (x₂ * y₂)) ^ k ∨ q w₂ = (q (x₂ * y₂)) ^ k * q x₂ := by
    refine ⟨k₂, ?_⟩
    rcases hk₂ with h | h
    · left; rw [h, map_zpow]
    · right; rw [h, map_mul, map_zpow]
  have hone := abs_two hqx₁ hqx₂ hqxc₁ hqxc₂ hqc₁ hqc₂ hq12 hq1c2 hq2c1 hne₁ hne₂ hqw₁ hqw₂ hu2'
    hcomm'
  apply huO
  refine (hq1 _).1 ?_
  rw [map_mul q r (w₁ * w₂), hqr, one_mul, map_mul q w₁ w₂]
  exact hone

end Two

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
