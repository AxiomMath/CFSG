module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AY11B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Y11C

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_cent_mul (h : L41GPh10 t L S x₁ x₂ lam rho) {X : Subgroup G}
    (hXR : X ≤ l41R t x₁ x₂ rho) {r k : G} (hr : r ∈ l41R t x₁ x₂ rho)
    (hcent : ∀ x ∈ X, r * k * x = x * (r * k)) : ∀ x ∈ X, k * x = x * k := by
  intro x hx
  have hrx : r * x = x * r := m13_comm_R h hr (hXR hx)
  apply mul_left_cancel (a := r)
  calc r * (k * x) = r * k * x := (mul_assoc _ _ _).symm
    _ = x * (r * k) := hcent x hx
    _ = (x * r) * k := (mul_assoc _ _ _).symm
    _ = (r * x) * k := by rw [hrx]
    _ = r * (x * k) := mul_assoc _ _ _

theorem m11_cent_V_cases (h : L41GPh10 t L S x₁ x₂ lam rho) {X : Subgroup G}
    (hXR : X ≤ l41R t x₁ x₂ rho) (hXρ : ∀ x ∈ X, rho * x * rho⁻¹ ∈ X) (hX : X ≠ ⊥) {g : G}
    (hgV : g ∈ l41V S t x₁ x₂) (hg : ∀ x ∈ X, g * x = x * g) :
    g ∈ l41R t x₁ x₂ rho ∨
      ((∃ r ∈ l41R t x₁ x₂ rho, g = r * t) ∧ ∀ x ∈ X, t * x = x * t) := by
  have hfix : ∀ x ∈ X, rho * x = x * rho → x = 1 := fun x hx hxρ =>
    m11_fix_R h.toL41GPh8 (hXR hx) hxρ
  have hρ3 := n4_rho_cube h.toCtx0
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  rcases m11_mem_V_cases h.toL41GPh8 hgV with ⟨r, hr, hg1 | hg1 | hg1 | hg1⟩
  · left
    rw [hg1]
    exact hr
  · right
    subst hg1
    exact ⟨⟨r, hr, rfl⟩, m11_cent_mul h hXR hr hg⟩
  · exfalso
    subst hg1
    exact hX (m11_eq_bot_of_inverting_centralizes X hXρ hρ3 h.lam_rho hfix
      (m11_cent_mul h hXR hr hg))
  · exfalso
    subst hg1
    rw [htl] at hg
    exact hX (m11_eq_bot_of_inverting_centralizes X hXρ hρ3 (m11_lamt_rho h.toL41GPh5) hfix
      (m11_cent_mul h hXR hr hg))

theorem m11_R_ne_bot (h : L41GPh8 t L S x₁ x₂ lam rho) : l41R t x₁ x₂ rho ≠ ⊥ := fun hb => by
  have := h.rfacts.card_R
  rw [hb, Subgroup.card_bot] at this
  norm_num at this

theorem m11_Y_ne_bot (h : L41GPh10 t L S x₁ x₂ lam rho) : l41Y t x₁ x₂ rho ≠ ⊥ := fun hb => by
  have := m11_card_Y h
  rw [hb, Subgroup.card_bot] at this
  norm_num at this

theorem m11_F2_ne_bot (h : Ctx0 t L S x₁ x₂ lam rho) : fourGrp x₁ x₂ ≠ ⊥ := fun hb => by
  have := n4_card_four h
  rw [hb, Subgroup.card_bot] at this
  norm_num at this

theorem m11_cent_V_R (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ centralizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : ∀ x ∈ l41R t x₁ x₂ rho, g * x = x * g := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hgc x hx).symm
    rcases m11_cent_V_cases h le_rfl (fun x hx => m11_rho_conj_R h.toL41GPh8 hx)
      (m11_R_ne_bot h.toL41GPh8) hgV hgc' with hR | ⟨-, ht⟩
    · exact hR
    · exfalso
      have hRB : l41R t x₁ x₂ rho ≤ baseGrp x₁ x₂ := by
        intro r hr
        rw [← h.rfacts.cent_t]
        exact Subgroup.mem_inf.mpr ⟨hr, mem_invCent_iff.mpr (ht r hr).symm⟩
      have := Subgroup.card_le_of_le hRB
      rw [h.rfacts.card_R, m13_card_B h.toCtx0] at this
      norm_num at this
  · intro r hr
    refine Subgroup.mem_inf.mpr ⟨m11_R_le_V h.toL41GPh8 hr, Subgroup.mem_centralizer_iff.mpr
      fun x hx => ?_⟩
    exact m13_comm_R h hx hr

theorem m11_cent_V_Y (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : ∀ x ∈ l41Y t x₁ x₂ rho, g * x = x * g := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hgc x hx).symm
    rcases m11_cent_V_cases h (m13_Y_le_R t x₁ x₂ rho) (fun x hx => m11_rho_conj_Y h hx)
      (m11_Y_ne_bot h) hgV hgc' with hR | ⟨-, ht⟩
    · exact hR
    · exfalso
      have hYF : l41Y t x₁ x₂ rho ≤ fourGrp x₁ x₂ := by
        rw [← m11_Y_inf_cent_t h]
        intro y hy
        exact Subgroup.mem_inf.mpr ⟨hy, mem_invCent_iff.mpr (ht y hy).symm⟩
      have := Subgroup.card_le_of_le hYF
      rw [m11_card_Y h, n4_card_four h.toCtx0] at this
      norm_num at this
  · intro r hr
    refine Subgroup.mem_inf.mpr ⟨m11_R_le_V h.toL41GPh8 hr, Subgroup.mem_centralizer_iff.mpr
      fun x hx => ?_⟩
    exact m13_comm_R h (m13_Y_le_R t x₁ x₂ rho hx) hr

theorem m11_cent_V_F2 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) = l41F t x₁ x₂ rho := by
  have htF2 : ∀ x ∈ fourGrp x₁ x₂, t * x = x * t := fun x hx =>
    m13_t_comm_base h.toL41GPh5 (m11_fourGrp_le_B x₁ x₂ hx)
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : ∀ x ∈ fourGrp x₁ x₂, g * x = x * g := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hgc x hx).symm
    rcases m11_cent_V_cases h h.rfacts.fourGrp_le (fun x hx => m11_rho_conj_F2 h.toL41GPh8 hx)
      (m11_F2_ne_bot h.toCtx0) hgV hgc' with hR | ⟨⟨r, hr, hgr⟩, -⟩
    · exact Subgroup.mem_sup_left hR
    · rw [hgr]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers t))
  · have hFV : l41F t x₁ x₂ rho ≤ l41V S t x₁ x₂ := by
      refine sup_le (m11_R_le_V h.toL41GPh8) ?_
      exact Subgroup.zpowers_le.mpr (m11_t_mem_V h.toL41GPh8)
    have hFc : l41F t x₁ x₂ rho ≤ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      refine sup_le (fun r hr => Subgroup.mem_centralizer_iff.mpr fun x hx => ?_) ?_
      · exact m13_comm_R h (h.rfacts.fourGrp_le hx) hr
      · refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
        exact (htF2 x hx).symm
    exact fun g hg => Subgroup.mem_inf.mpr ⟨hFV hg, hFc hg⟩

theorem m11_center_F (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41F t x₁ x₂ rho ⊓ centralizer ((l41F t x₁ x₂ rho : Subgroup G) : Set G) =
      baseGrp x₁ x₂ := by
  rw [m13_cent_F h]
  exact inf_eq_right.mpr ((n4_base_le_R h.toL41GPh3).trans le_sup_left)

theorem m11_F2_cases {y z g : G} (hy : y * y = 1) (hz : z * z = 1) (hyz : y * z = z * y)
    (hg : g ∈ closure ({y, z} : Set G)) : g = 1 ∨ g = y ∨ g = z ∨ g = y * z :=
  (m11_mem_closure_pair_iff hy hz hyz).mp hg

theorem m11_lam_conj_y (h : WreathRel x₁ x₂ lam) :
    lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  calc lam * x₁ ^ 2 * lam⁻¹ = (lam * x₁ * lam⁻¹) ^ 2 := conj_pow.symm
    _ = x₂ ^ 2 := by rw [h.conj_x₁]
    _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := h.x₂_sq

theorem m11_lam_conj_z (h : WreathRel x₁ x₂ lam) : lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
  have h2 : lam * x₂ * lam⁻¹ = x₁ := by
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h.conj_x₁]
      _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
      _ = x₁ := by
        have hl2 : lam * lam = 1 := by
          have := pow_orderOf_eq_one lam
          rwa [h.ord_lam, pow_two] at this
        rw [hl2]
        group
  calc lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (lam * (x₁ * x₂) * lam⁻¹) ^ 2 := conj_pow.symm
    _ = (lam * x₁ * lam⁻¹ * (lam * x₂ * lam⁻¹)) ^ 2 := by congr 1; group
    _ = (x₂ * x₁) ^ 2 := by rw [h.conj_x₁, h2]
    _ = (x₁ * x₂) ^ 2 := by rw [h.comm]

theorem m11_cent_F2_lam (h : Ctx0 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ fourGrp x₁ x₂)
    (hc : lam * g = g * lam) : g = 1 ∨ g = (x₁ * x₂) ^ 2 := by
  have hy : x₁ ^ 2 * x₁ ^ 2 = 1 := m11_fourGrp_sq h (Subgroup.subset_closure (by simp))
  have hz : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := h.wreath.sq_x₁x₂_mul_self
  have hyz : x₁ ^ 2 * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * x₁ ^ 2 :=
    baseGrp_comm h.wreath (m11_fourGrp_le_B x₁ x₂ (Subgroup.subset_closure (by simp)))
      (m11_fourGrp_le_B x₁ x₂ (Subgroup.subset_closure (by simp)))
  have hzne : (x₁ * x₂) ^ 2 ≠ 1 := h.wreath.sq_x₁x₂_ne_one
  have hly := m11_lam_conj_y h.wreath
  have hlz := m11_lam_conj_z h.wreath
  have hcy : ∀ u : G, lam * u = u * lam → lam * u * lam⁻¹ = u := fun u hu => by
    rw [hu]
    group
  rcases m11_F2_cases hy hz hyz hg with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso
    have := (hcy _ hc).symm.trans hly
    exact hzne (mul_left_cancel (a := x₁ ^ 2) (by rw [mul_one]; exact this.symm))
  · exact Or.inr rfl
  · exfalso
    have h1 : lam * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam⁻¹ = x₁ ^ 2 := by
      calc lam * (x₁ ^ 2 * (x₁ * x₂) ^ 2) * lam⁻¹
          = (lam * x₁ ^ 2 * lam⁻¹) * (lam * (x₁ * x₂) ^ 2 * lam⁻¹) := by group
        _ = (x₁ ^ 2 * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 := by rw [hly, hlz]
        _ = x₁ ^ 2 := by rw [mul_assoc, hz, mul_one]
    have h2 := (hcy _ hc).symm.trans h1
    exact hzne (mul_left_cancel (a := x₁ ^ 2) (by rw [mul_one]; exact h2))

theorem m11_z_comm_V (h : L41GPh8 t L S x₁ x₂ lam rho) {v : G} (hv : v ∈ l41V S t x₁ x₂) :
    (x₁ * x₂) ^ 2 * v = v * (x₁ * x₂) ^ 2 := by
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzB : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := m11_fourGrp_le_B x₁ x₂ hzF
  have hzt : (x₁ * x₂) ^ 2 * t = t * (x₁ * x₂) ^ 2 := (m13_t_comm_base h.toL41GPh5 hzB).symm
  have hzl : (x₁ * x₂) ^ 2 * lam = lam * (x₁ * x₂) ^ 2 := by
    have := m11_lam_conj_z h.wreath
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  obtain ⟨r, hr, hv'⟩ := m11_mem_V_cases h hv
  have hzr : (x₁ * x₂) ^ 2 * r = r * (x₁ * x₂) ^ 2 := h.rfacts.fourGrp_central _ hzF r hr
  have hcomb : ∀ k : G, (x₁ * x₂) ^ 2 * k = k * (x₁ * x₂) ^ 2 →
      (x₁ * x₂) ^ 2 * (r * k) = (r * k) * (x₁ * x₂) ^ 2 := by
    intro k hk
    calc (x₁ * x₂) ^ 2 * (r * k) = ((x₁ * x₂) ^ 2 * r) * k := (mul_assoc _ _ _).symm
      _ = (r * (x₁ * x₂) ^ 2) * k := by rw [hzr]
      _ = r * ((x₁ * x₂) ^ 2 * k) := mul_assoc _ _ _
      _ = r * (k * (x₁ * x₂) ^ 2) := by rw [hk]
      _ = (r * k) * (x₁ * x₂) ^ 2 := (mul_assoc _ _ _).symm
  have hztl : (x₁ * x₂) ^ 2 * (t * lam) = (t * lam) * (x₁ * x₂) ^ 2 := by
    calc (x₁ * x₂) ^ 2 * (t * lam) = ((x₁ * x₂) ^ 2 * t) * lam := (mul_assoc _ _ _).symm
      _ = (t * (x₁ * x₂) ^ 2) * lam := by rw [hzt]
      _ = t * ((x₁ * x₂) ^ 2 * lam) := mul_assoc _ _ _
      _ = t * (lam * (x₁ * x₂) ^ 2) := by rw [hzl]
      _ = (t * lam) * (x₁ * x₂) ^ 2 := (mul_assoc _ _ _).symm
  rcases hv' with hv' | hv' | hv' | hv' <;> rw [hv']
  · exact hzr
  · exact hcomb t hzt
  · exact hcomb lam hzl
  · exact hcomb (t * lam) hztl

theorem m11_cent_Y_V (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41Y t x₁ x₂ rho ⊓ centralizer ((l41V S t x₁ x₂ : Subgroup G) : Set G) =
      zpowers ((x₁ * x₂) ^ 2) := by
  have hzF : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro g hg
    obtain ⟨hgY, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgt : g ∈ invCent t := by
      rw [mem_invCent_iff]
      exact (Subgroup.mem_centralizer_iff.mp hgc t (m11_t_mem_V h.toL41GPh8)).symm
    have hgF : g ∈ fourGrp x₁ x₂ := by
      rw [← m11_Y_inf_cent_t h]
      exact Subgroup.mem_inf.mpr ⟨hgY, hgt⟩
    have hgl : lam * g = g * lam :=
      Subgroup.mem_centralizer_iff.mp hgc lam (m11_lam_mem_V h.toL41GPh8)
    rcases m11_cent_F2_lam h.toCtx0 hgF hgl with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨m11_fourGrp_le_Y h hzF, Subgroup.mem_centralizer_iff.mpr
      fun v hv => ?_⟩
    exact (m11_z_comm_V h.toL41GPh8 hv).symm

end Y11C

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
