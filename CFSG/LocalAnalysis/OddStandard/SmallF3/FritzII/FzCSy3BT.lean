module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BRE

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

theorem fzc_sy3_P_le_R (hq : FzCQFacts t S x₁ x₂ lam rho) :
    fzP t x₁ x₂ rho ≤ fzR t x₁ x₂ :=
  le_of_le_of_eq le_sup_left hq.R_eq_PK.symm

theorem fzc_sy3_rho3 (h : Ctx0 t L S x₁ x₂ lam rho) : rho ^ 3 = 1 := by
  rw [← h.ord_rho]
  exact pow_orderOf_eq_one rho

theorem fzc_sy3_rho_comm_t (h : Ctx0 t L S x₁ x₂ lam rho) : rho * t = t * rho := by
  calc rho * t = rho * t * rho⁻¹ * rho := by group
    _ = t * rho := by rw [fzc_sy2_rho_t h]

theorem fzc_sy3_rho_inv_conj (h : Ctx0 t L S x₁ x₂ lam rho) (u : G) :
    rho⁻¹ * u * rho = rho * (rho * u * rho⁻¹) * rho⁻¹ := by
  have hri : rho⁻¹ = rho * rho := by
    rw [inv_eq_iff_mul_eq_one]
    calc rho * (rho * rho) = rho ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
      _ = 1 := fzc_sy3_rho3 h
  calc rho⁻¹ * u * rho = rho⁻¹ * u * rho⁻¹⁻¹ := by rw [inv_inv]
    _ = rho * rho * u * (rho * rho)⁻¹ := by rw [hri]
    _ = rho * (rho * u * rho⁻¹) * rho⁻¹ := by group

theorem fzc_sy3_t_comm_tE (h : Ctx0 t L S x₁ x₂ lam rho) {u : G}
    (hu : t * u ∈ baseGrp x₁ x₂) : u * t = t * u := by
  have hc := S4A.pt_comm_base h t h.hyp.mem_twoCore _ hu
  calc u * t = t⁻¹ * ((t * u) * t) := by group
    _ = t⁻¹ * (t * (t * u)) := by rw [hc]
    _ = t * u := by group

theorem fzc_sy3_t_comm_Et (h : Ctx0 t L S x₁ x₂ lam rho) {u : G}
    (hu : u * t ∈ baseGrp x₁ x₂) : u * t = t * u := by
  have hc := S4A.pt_comm_base h t h.hyp.mem_twoCore _ hu
  calc u * t = (u * t * t) * t⁻¹ := by group
    _ = (t * (u * t)) * t⁻¹ := by rw [hc]
    _ = t * u := by group

theorem fzc_sy3_tE_mul (h : Ctx0 t L S x₁ x₂ lam rho) {u v : G}
    (hu : t * u ∈ baseGrp x₁ x₂) (hv : t * v ∈ baseGrp x₁ x₂) : u * v ∈ baseGrp x₁ x₂ := by
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have hc : t * (t * u) = (t * u) * t := S4A.pt_comm_base h t h.hyp.mem_twoCore _ hu
  have e : u * v = (t * u) * (t * v) := by
    calc u * v = t * (t * u) * v := by rw [← mul_assoc, htt, one_mul]
      _ = (t * u) * t * v := by rw [hc]
      _ = (t * u) * (t * v) := by group
  rw [e]
  exact mul_mem hu hv

theorem fzc_sy3_E_tE (h : Ctx0 t L S x₁ x₂ lam rho) {u v : G}
    (hu : u ∈ baseGrp x₁ x₂) (hv : t * v ∈ baseGrp x₁ x₂) : t * (u * v) ∈ baseGrp x₁ x₂ := by
  rw [← mul_assoc, S4A.pt_comm_base h t h.hyp.mem_twoCore u hu, mul_assoc]
  exact mul_mem hu hv

theorem fzc_sy3_rho_tE (h : Ctx0 t L S x₁ x₂ lam rho) {u : G}
    (hu : t * u ∈ baseGrp x₁ x₂) : t * (rho * u * rho⁻¹) ∈ baseGrp x₁ x₂ := by
  have e : t * (rho * u * rho⁻¹) = rho * (t * u) * rho⁻¹ := by
    calc t * (rho * u * rho⁻¹) = (rho * t * rho⁻¹) * (rho * u * rho⁻¹) := by
          rw [fzc_sy2_rho_t h]
      _ = rho * (t * u) * rho⁻¹ := by group
  rw [e]
  exact fzc_sy2_rho_nrm_E h _ hu

theorem fzc_sy3_R_nrm_E (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) :
    ∀ r ∈ fzR t x₁ x₂, ∀ e ∈ baseGrp x₁ x₂, r * e * r⁻¹ ∈ baseGrp x₁ x₂ := by
  intro r hr e he
  have e1 : r * e * r⁻¹ = (r * e * r⁻¹ * e⁻¹) * e := by group
  rw [e1]
  exact mul_mem (S4A.pt_four_le_base x₁ x₂ (fzc_sy3_R_E h hq hK hq4 hqt r hr e he)) he

theorem fzc_sy3_R_tE (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) :
    ∀ r ∈ fzR t x₁ x₂, ∀ u : G, t * u ∈ baseGrp x₁ x₂ →
      t * (r * u * r⁻¹) ∈ baseGrp x₁ x₂ := by
  intro r hr u hu
  obtain ⟨f, hf, hrt⟩ := hq.R_act_t r hr
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have e : t * (r * u * r⁻¹) = (t * t) * f * (r * (t * u) * r⁻¹) := by
    calc t * (r * u * r⁻¹) = t * (r * ((t * t) * u) * r⁻¹) := by rw [htt, one_mul]
      _ = t * (r * t * r⁻¹) * (r * (t * u) * r⁻¹) := by group
      _ = t * (t * f) * (r * (t * u) * r⁻¹) := by rw [hrt]
      _ = (t * t) * f * (r * (t * u) * r⁻¹) := by group
  rw [e, htt, one_mul]
  exact mul_mem (S4A.pt_four_le_base x₁ x₂ hf) (fzc_sy3_R_nrm_E h hq hK hq4 hqt r hr _ hu)

theorem fzc_sy3_z_ne_one (h : Ctx0 t L S x₁ x₂ lam rho) : (x₁ * x₂) ^ 2 ≠ 1 := by
  intro hz
  have hc : Commute x₁ x₂ := h.wreath.comm
  have e1 : x₁ ^ 2 = (x₂ ^ 2)⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv, ← hc.mul_pow]
    exact hz
  have h2 : x₁ ^ 2 ∈ zpowers x₂ := by
    rw [e1]
    exact inv_mem (pow_mem (mem_zpowers x₂) 2)
  have hmem : x₁ ^ 2 ∈ zpowers x₁ ⊓ zpowers x₂ :=
    Subgroup.mem_inf.2 ⟨pow_mem (mem_zpowers x₁) 2, h2⟩
  rw [h.wreath.inf_eq_bot, mem_bot] at hmem
  have h4 := orderOf_dvd_of_pow_eq_one hmem
  rw [h.wreath.ord_x₁] at h4
  exact absurd h4 (by norm_num)

theorem fzc_sy3_sq_coset (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    ∀ s ∈ fzR t x₁ x₂, ∀ w ∈ baseGrp x₁ x₂ ⊔ zpowers t,
      (w * s) ^ 2 * (s ^ 2)⁻¹ ∈ fourGrp x₁ x₂ := by
  intro s hs w hw
  have htt : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
  have hEc : ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := fun a ha b hb =>
    fzc_sy2_W_comm h a (mem_sup_right ha) b (mem_sup_right hb)
  have hE : ∀ e ∈ baseGrp x₁ x₂, e * (s * e * s⁻¹) ∈ fourGrp x₁ x₂ := by
    intro e he
    have hζ := fzc_sy3_R_E h hq hK hq4 hqt s hs e he
    have hc := hEc e he _ (S4A.pt_four_le_base x₁ x₂ hζ)
    have e2 : e * (s * e * s⁻¹) = (s * e * s⁻¹ * e⁻¹) * e ^ 2 := by
      calc e * (s * e * s⁻¹) = e * (s * e * s⁻¹ * e⁻¹) * e := by group
        _ = (s * e * s⁻¹ * e⁻¹) * e * e := by rw [hc]
        _ = (s * e * s⁻¹ * e⁻¹) * e ^ 2 := by group
    rw [e2]
    exact mul_mem hζ (fzc_sy2_E_sq h e he)
  have heq : (w * s) ^ 2 * (s ^ 2)⁻¹ = w * (s * w * s⁻¹) := by simp only [pow_two]; group
  rw [heq]
  rcases (fzc_sy3_Wp_mem h).1 hw with hwE | hwE
  · exact hE w hwE
  · obtain ⟨f, hf, hst⟩ := hq.R_act_t s hs
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ baseGrp x₁ x₂, w = t * e :=
      ⟨t * w, hwE, by rw [← mul_assoc, htt, one_mul]⟩
    have hte : t * e = e * t := S4A.pt_comm_base h t h.hyp.mem_twoCore e he
    have hfe : e * f = f * e := hEc e he f (S4A.pt_four_le_base x₁ x₂ hf)
    have e3 : t * e * (s * (t * e) * s⁻¹) = f * (e * (s * e * s⁻¹)) := by
      calc t * e * (s * (t * e) * s⁻¹) = t * e * (s * t * s⁻¹) * (s * e * s⁻¹) := by group
        _ = t * e * (t * f) * (s * e * s⁻¹) := by rw [hst]
        _ = (t * e) * t * f * (s * e * s⁻¹) := by group
        _ = e * t * t * f * (s * e * s⁻¹) := by rw [hte]
        _ = e * (t * t) * f * (s * e * s⁻¹) := by group
        _ = e * f * (s * e * s⁻¹) := by rw [htt, mul_one]
        _ = f * e * (s * e * s⁻¹) := by rw [hfe]
        _ = f * (e * (s * e * s⁻¹)) := by group
    rw [e3]
    exact mul_mem hf (hE e he)

end CFSG.OddStandard.SmallF3.FritzII
