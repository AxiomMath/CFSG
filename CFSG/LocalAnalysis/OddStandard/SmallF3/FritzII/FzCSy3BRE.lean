module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQDef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

theorem fzc_sy3_R_E (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    ∀ r ∈ fzR t x₁ x₂, ∀ e ∈ baseGrp x₁ x₂, r * e * r⁻¹ * e⁻¹ ∈ fourGrp x₁ x₂ := by
  intro r hr e he
  have hWcomm := fzc_sy2_W_comm h
  have hEW : baseGrp x₁ x₂ ≤ ctxW t x₁ x₂ := le_sup_right
  have hreW : r * e * r⁻¹ ∈ ctxW t x₁ x₂ := fzc_sy3_R_W r hr e (hEW he)
  have heiW : e⁻¹ ∈ ctxW t x₁ x₂ := (ctxW t x₁ x₂).inv_mem (hEW he)
  have hdW : r * e * r⁻¹ * e⁻¹ ∈ ctxW t x₁ x₂ := (ctxW t x₁ x₂).mul_mem hreW heiW
  have hd2 : (r * e * r⁻¹ * e⁻¹) ^ 2 = 1 := by
    have hcomm : Commute (r * e * r⁻¹) e⁻¹ := hWcomm _ hreW _ heiW
    have hsq : (r * e * r⁻¹ * e⁻¹) ^ 2 = (r * e * r⁻¹) ^ 2 * (e⁻¹) ^ 2 := hcomm.mul_pow 2
    have ha2 : (r * e * r⁻¹) ^ 2 = r * e ^ 2 * r⁻¹ := by simp only [pow_two]; group
    have hc := hq.R_cent_fourGrp r hr (e ^ 2) (fzc_sy2_E_sq h e he)
    have h3 : r * e ^ 2 * r⁻¹ = e ^ 2 := by rw [hc]; group
    rw [hsq, ha2, h3]
    simp [inv_pow]
  obtain ⟨k, e₁, he₁, hk4, hd⟩ := fzc_sy3_W_dec h hK hq4 _ hdW
  have hqcomm : Commute q e₁ := fzc_sy3_q_comm_W h hK e₁ (hEW he₁)
  have hdd : q ^ (2 * k) * e₁ ^ 2 = 1 := by
    have hsq : (q ^ k * e₁) ^ 2 = (q ^ k) ^ 2 * e₁ ^ 2 := (hqcomm.pow_left k).mul_pow 2
    have hpow : (q ^ k) ^ 2 = q ^ (2 * k) := by
      rw [← pow_mul, Nat.mul_comm k 2]
    have h := hd2
    rw [hd, hsq, hpow] at h
    exact h
  have he₁E2 : e₁ ^ 2 ∈ baseGrp x₁ x₂ :=
    S4A.pt_four_le_base x₁ x₂ (fzc_sy2_E_sq h e₁ he₁)
  have hqE : q ^ (2 * k) ∈ baseGrp x₁ x₂ := by
    have hqeq : q ^ (2 * k) = (e₁ ^ 2)⁻¹ := mul_eq_one_iff_eq_inv.mp hdd
    rw [hqeq]
    exact Subgroup.inv_mem _ he₁E2
  have hdiv : 4 ∣ 2 * k := fzc_sy3_qpow_E h hK hq4 hqE
  have hk02 : k = 0 ∨ k = 2 := by
    interval_cases k
    · left; rfl
    · exfalso; norm_num at hdiv
    · right; rfl
    · exfalso; norm_num at hdiv
  rcases hk02 with rfl | rfl
  · have he₁sq : e₁ ^ 2 = 1 := by
      have h := hdd
      simpa using h
    have he₁Z : e₁ ∈ fourGrp x₁ x₂ := fzc_sy2_E_invol h e₁ he₁ he₁sq
    have hone : r * e * r⁻¹ * e⁻¹ = e₁ := by simpa using hd
    rw [hone]
    exact he₁Z
  · have hq4' : q ^ 4 = 1 := by simpa [hq4] using pow_orderOf_eq_one q
    have he₁sq : e₁ ^ 2 = 1 := by
      have h := hdd
      rw [show (2 : ℕ) * 2 = 4 from rfl, hq4', one_mul] at h
      exact h
    have he₁Z : e₁ ∈ fourGrp x₁ x₂ := fzc_sy2_E_invol h e₁ he₁ he₁sq
    have he₁E : e₁ ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ he₁Z
    obtain ⟨f, hfZ, hrt⟩ := hq.R_act_t r hr
    have hfE : f ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hfZ
    have hr2W : r * r ∈ ctxW t x₁ x₂ := hq.R_sq_mem_W r hr
    have htW : t ∈ ctxW t x₁ x₂ := fzc_sy2_t_mem h
    have ht2 : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
    have he₁mul : e₁ * e₁ = 1 := by rw [← pow_two]; exact he₁sq
    have hL : r * r * e * (r * r)⁻¹ = e := by
      have hc := hWcomm (r * r) hr2W e (hEW he)
      rw [hc]; group
    have hre : r * e * r⁻¹ = t * e₁ * e := by
      calc r * e * r⁻¹ = (r * e * r⁻¹ * e⁻¹) * e := by group
        _ = q ^ 2 * e₁ * e := by rw [hd]
        _ = t * e₁ * e := by rw [hqt]
    have hre₁ : r * e₁ * r⁻¹ = e₁ := by
      have hc := hq.R_cent_fourGrp r hr e₁ he₁Z
      rw [hc]; group
    have hR : r * r * e * (r * r)⁻¹ = f * e := by
      have h1 : r * r * e * (r * r)⁻¹ = r * (r * e * r⁻¹) * r⁻¹ := by group
      rw [h1, hre]
      calc r * (t * e₁ * e) * r⁻¹
          = (r * t * r⁻¹) * (r * e₁ * r⁻¹) * (r * e * r⁻¹) := by group
        _ = (t * f) * e₁ * (t * e₁ * e) := by rw [hrt, hre₁, hre]
        _ = f * e := by
              have htf : t * f = f * t := S4A.pt_comm_base h t h.hyp.mem_twoCore f hfE
              have hte₁ : t * e₁ = e₁ * t := S4A.pt_comm_base h t h.hyp.mem_twoCore e₁ he₁E
              calc (t * f) * e₁ * (t * e₁ * e)
                  = t * f * e₁ * t * e₁ * e := by group
                _ = t * f * (e₁ * t) * e₁ * e := by group
                _ = t * f * (t * e₁) * e₁ * e := by rw [← hte₁]
                _ = t * (f * t) * e₁ * e₁ * e := by group
                _ = t * (t * f) * e₁ * e₁ * e := by rw [← htf]
                _ = t * t * (f * (e₁ * e₁) * e) := by group
                _ = f * e := by rw [ht2, he₁mul]; group
    have hfe : f * e = e := by rw [← hR, hL]
    have hf1 : f = 1 := by
      have h : f * e = 1 * e := by rw [one_mul]; exact hfe
      exact mul_right_cancel h
    have hrt1 : r * t * r⁻¹ = t := by rw [hrt, hf1, mul_one]
    have hmem : r ∈ fzR t x₁ x₂ ⊓ invCent t := by
      refine Subgroup.mem_inf.mpr ⟨hr, ?_⟩
      show r ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc r * t = r * t * r⁻¹ * r := by group
        _ = t * r := by rw [hrt1]
    rw [hq.cent_R_t] at hmem
    have hone : r * e * r⁻¹ * e⁻¹ = 1 := by
      have hre' : r * e * r⁻¹ = e := by
        have hc := hWcomm r hmem e (hEW he)
        rw [hc]; group
      rw [hre']; group
    rw [hone]
    exact (fourGrp x₁ x₂).one_mem

theorem fzc_sy3_R_Wp (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t) :
    ∀ r ∈ fzR t x₁ x₂, ∀ w ∈ baseGrp x₁ x₂ ⊔ zpowers t,
      r * w * r⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro r hr w hw
  rw [fzc_sy3_Wp_mem h] at hw
  rcases hw with hwE | htwE
  · have hζZ := fzc_sy3_R_E h hq hK hq4 hqt r hr w hwE
    have hζE : r * w * r⁻¹ * w⁻¹ ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hζZ
    have hx : r * w * r⁻¹ = (r * w * r⁻¹ * w⁻¹) * w := by group
    rw [hx]
    exact Subgroup.mem_sup_left ((baseGrp x₁ x₂).mul_mem hζE hwE)
  · obtain ⟨f, hfZ, hrt⟩ := hq.R_act_t r hr
    have hfE : f ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hfZ
    have hζZ := fzc_sy3_R_E h hq hK hq4 hqt r hr (t * w) htwE
    have hζE : r * (t * w) * r⁻¹ * (t * w)⁻¹ ∈ baseGrp x₁ x₂ :=
      S4A.pt_four_le_base x₁ x₂ hζZ
    set ζ : G := r * (t * w) * r⁻¹ * (t * w)⁻¹ with hζ_def
    have he' : f * ζ * (t * w) ∈ baseGrp x₁ x₂ := by
      rw [hζ_def]
      exact (baseGrp x₁ x₂).mul_mem ((baseGrp x₁ x₂).mul_mem hfE hζE) htwE
    have ht2 : t * t = 1 := by rw [← pow_two]; exact fzc_sy2_t_sq h
    have hx : r * w * r⁻¹ = t * (f * ζ * (t * w)) := by
      have hwt : w = t * (t * w) := by rw [← mul_assoc, ht2, one_mul]
      have h2 : r * (t * w) * r⁻¹ = ζ * (t * w) := by rw [hζ_def]; group
      calc r * w * r⁻¹
          = r * (t * (t * w)) * r⁻¹ := by nth_rewrite 1 [hwt]; rfl
        _ = (r * t * r⁻¹) * (r * (t * w) * r⁻¹) := by group
        _ = (t * f) * (ζ * (t * w)) := by rw [hrt, h2]
        _ = t * (f * ζ * (t * w)) := by group
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left he')

end CFSG.OddStandard.SmallF3.FritzII
