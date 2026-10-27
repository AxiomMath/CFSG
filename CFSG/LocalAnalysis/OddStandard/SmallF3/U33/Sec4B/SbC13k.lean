module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13j

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_om_conj_aux (hc : Ctx13C t L S x₁ x₂ lam rho tau om) {b e : G}
    (hb : b ∈ baseGrp x₁ x₂) (he : e ∈ ctxYq t tau x₁ x₂ rho)
    (hce : e * (t * e * t⁻¹) = b ^ 2) :
    ∃ w ∈ fourGrp x₁ x₂, om * b * om⁻¹ = b * e * w := by
  have hA : Ctx13A t L S x₁ x₂ lam rho tau om := hc.toCtx13A
  have hB : Ctx13B t L S x₁ x₂ lam rho tau om := hc.toCtx13B
  obtain ⟨homM, hom2, homρ⟩ := c13_om_data hA
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2
  have hbQ : b ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q hb
  set q : G := om * b * om⁻¹ with hqdef
  have hqQ : q ∈ ctxQ t tau x₁ x₂ rho := hc.normal_Q.2 om homM b hbQ
  have hb_inv : t * b⁻¹ * t⁻¹ = b⁻¹ := c13_t_cent_B hc.toCtx11 b⁻¹ (Subgroup.inv_mem _ hb)
  have ht_om : t * om = om * (t * tau) := by
    have h1 : om * t * om = t * tau := by rw [← hc.t_om, hom_inv]
    calc t * om = (om * om) * t * om := by rw [hom2, one_mul]
      _ = om * (om * t * om) := by group
      _ = om * (t * tau) := by rw [h1]
  have hmid : (t * tau) * b * (t * tau)⁻¹ = b⁻¹ := by
    calc (t * tau) * b * (t * tau)⁻¹ = t * (tau * b * tau⁻¹) * t⁻¹ := by group
      _ = t * b⁻¹ * t⁻¹ := by rw [c13_tau_inv_B hA b hb]
      _ = b⁻¹ := hb_inv
  have htq : t * q * t⁻¹ = q⁻¹ := by
    calc t * q * t⁻¹ = (t * om) * b * (t * om)⁻¹ := by rw [hqdef]; group
      _ = (om * (t * tau)) * b * (om * (t * tau))⁻¹ := by rw [ht_om]
      _ = om * ((t * tau) * b * (t * tau)⁻¹) * om⁻¹ := by group
      _ = om * b⁻¹ * om⁻¹ := by rw [hmid]
      _ = (om * b * om⁻¹)⁻¹ := by group
      _ = q⁻¹ := by rw [hqdef]
  set a : G := b⁻¹ * q with hadef
  have haY : a ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hadef, hqdef]
    exact c13_triv_QY hB homM hom2 homρ b hbQ
  have hta : t * a * t⁻¹ = b⁻¹ * q⁻¹ := by
    calc t * a * t⁻¹ = (t * b⁻¹ * t⁻¹) * (t * q * t⁻¹) := by rw [hadef]; group
      _ = b⁻¹ * q⁻¹ := by rw [hb_inv, htq]
  have hacmap : a * (t * a * t⁻¹) = (b ^ 2)⁻¹ := by
    have hcomm : b⁻¹ * q = q * b⁻¹ :=
      hc.Q_comm b⁻¹ (Subgroup.inv_mem _ hbQ) q hqQ
    calc a * (t * a * t⁻¹) = (b⁻¹ * q) * (b⁻¹ * q⁻¹) := by rw [hadef, hta]
      _ = b⁻¹ * (q * b⁻¹) * q⁻¹ := by group
      _ = b⁻¹ * (b⁻¹ * q) * q⁻¹ := by rw [hcomm]
      _ = b⁻¹ * b⁻¹ * (q * q⁻¹) := by group
      _ = b⁻¹ * b⁻¹ := by group
      _ = (b ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
  have haeY : a * e ∈ ctxYq t tau x₁ x₂ rho := mul_mem haY he
  have haecmap : (a * e) * (t * (a * e) * t⁻¹) = 1 := by
    rw [c13_cmap_mul hc a haY e he, hacmap, hce]
    group
  have hwV : a * e ∈ fourGrp x₁ x₂ := (c13_cmap_eq_one hc (a * e) haeY).mp haecmap
  set w : G := a * e with hwdef
  have he2 : e * e = 1 := by
    have h := hc.Y_elem.2 e he
    simpa [pow_two] using h
  have ha_we : a = w * e := by
    calc a = a * 1 := (mul_one a).symm
      _ = a * (e * e) := by rw [he2]
      _ = (a * e) * e := by group
      _ = w * e := by rw [hwdef]
  have hwe : w * e = e * w :=
    hc.Q_comm w (ctxYq_le_ctxQ (hc.V_le_Y hwV)) e (ctxYq_le_ctxQ he)
  refine ⟨w, hwV, ?_⟩
  calc om * b * om⁻¹ = q := hqdef.symm
    _ = b * a := by rw [hadef]; group
    _ = b * (w * e) := by rw [ha_we]
    _ = b * e * w := by rw [hwe, mul_assoc]

theorem c13_om_x {v₀ v₂ : G}
    (hc : Ctx13C t L S x₁ x₂ lam rho tau om)
    (hv₀Y : v₀ ∈ ctxYq t tau x₁ x₂ rho) (hv₀V : v₀ ∉ fourGrp x₁ x₂)
    (hσ : (lam * t) * v₀ * (lam * t)⁻¹ = v₀) (hv₂ : v₂ ∈ orbitGrp rho v₀)
    (ht : t * v₂ * t⁻¹ = v₂ * x₁ ^ 2) :
    (∃ w ∈ fourGrp x₁ x₂, om * x₁ * om⁻¹ = x₁ * v₂ * w) ∧
      (∃ w ∈ fourGrp x₁ x₂, om * x₂ * om⁻¹ = x₂ * v₀ * v₂ * w) := by
  have hv₂Y : v₂ ∈ ctxYq t tau x₁ x₂ rho := (c13_V'_props hc hv₀Y hv₀V hσ).1 hv₂
  have hv₂2 : v₂ * v₂ = 1 := by
    have h := hc.Y_elem.2 v₂ hv₂Y
    simpa [pow_two] using h
  have hyY : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho :=
    hc.V_le_Y (Subgroup.subset_closure (by simp))
  have hzY : (x₁ * x₂) ^ 2 ∈ ctxYq t tau x₁ x₂ rho :=
    hc.V_le_Y (Subgroup.subset_closure (by simp))
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hcv₂ : v₂ * (t * v₂ * t⁻¹) = x₁ ^ 2 := by
    rw [ht, ← mul_assoc, hv₂2, one_mul]
  have hcv₀ : v₀ * (t * v₀ * t⁻¹) = (x₁ * x₂) ^ 2 := by
    have hv₀2 : v₀ * v₀ = 1 := by
      have h := hc.Y_elem.2 v₀ hv₀Y
      simpa [pow_two] using h
    rw [c13_v0_t hc hv₀Y hv₀V hσ, ← mul_assoc, hv₀2, one_mul]
  have hce₂ : (v₀ * v₂) * (t * (v₀ * v₂) * t⁻¹) = x₂ ^ 2 := by
    rw [c13_cmap_mul hc v₀ hv₀Y v₂ hv₂Y, hcv₀, hcv₂, hc.wreath.x₂_sq]
    exact hc.Q_comm _ (ctxYq_le_ctxQ hzY) _ (ctxYq_le_ctxQ hyY)
  refine ⟨?_, ?_⟩
  · exact c13_om_conj_aux hc hx₁B hv₂Y hcv₂
  · have he : v₀ * v₂ ∈ ctxYq t tau x₁ x₂ rho := mul_mem hv₀Y hv₂Y
    obtain ⟨w, hw, hwq⟩ := c13_om_conj_aux hc hx₂B he hce₂
    exact ⟨w, hw, by rw [hwq]; group⟩

theorem c13_data_V (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∃ (V' : Subgroup G) (v₁ v₂ : G), Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂ := by
  obtain ⟨v₀, hv₀Y, hv₀V, hσ⟩ := c13_exists_v0 hc.toCtx13B
  obtain ⟨v₂, hv₂, ht⟩ := c13_exists_v2 hc hv₀Y hv₀V hσ
  obtain ⟨hle, hel, hcard, hρ, hlt, hinf, hsup, hcent⟩ := c13_V'_props hc hv₀Y hv₀V hσ
  obtain ⟨hQ, hBV'⟩ := c13_Q_B_V' hc hv₀Y hv₀V hσ
  obtain ⟨hv2n, hgen⟩ := c13_v2_facts hc hv₀Y hv₀V hσ hv₂ ht
  obtain ⟨h18, h19⟩ := c13_om_x hc hv₀Y hv₀V hσ hv₂ ht
  refine ⟨orbitGrp rho v₀, v₀, v₂, ?_⟩
  have hv₁V' : v₀ ∈ orbitGrp rho v₀ := Subgroup.subset_closure (by simp)
  have hv₁ne : v₀ ≠ 1 := by
    intro h
    exact hv₀V (by rw [h]; exact Subgroup.one_mem _)
  have hvt : t * v₀ * t⁻¹ = v₀ * (x₁ * x₂) ^ 2 := c13_v0_t hc hv₀Y hv₀V hσ
  have hsig : (lam * t) * v₂ * (lam * t)⁻¹ = v₂ * v₀ :=
    c13_sigma_v2 hc hv₀Y hv₀V hσ hv₂ ht
  have hCQ : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) =
      closure ({x₁ * v₂, x₂ * v₀ * v₂} : Set G) :=
    c13_CQ_ttau hc hv₀Y hv₀V hσ hv₂ ht
  unfold Ctx13V
  exact ⟨hel, hcard, hQ, hBV', hρ, hlt, hsup.symm, hcent, hv₁V', hv₁ne, hvt,
    hv₂, hv2n, hgen, ht, hsig, hCQ, h18, h19⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
