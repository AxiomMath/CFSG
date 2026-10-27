module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem l17_tau_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    tau ∉ ctxP t tau x₁ x₂ rho := by
  intro htau
  have hcent : tau ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp htau).2
  obtain ⟨a, ha, hane⟩ := IsZ4Z4E4.exists_sq_ne_one hc.q_iso
  apply hane
  have hcomm : a * tau = tau * a :=
    Subgroup.mem_centralizer_iff.mp hcent a ha
  have hconj : tau * a * tau⁻¹ = a := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hinv : a = a⁻¹ := by
    rw [← hc.tau_inv_Q a ha, hconj]
  rw [pow_two]
  exact mul_eq_one_iff_eq_inv.mpr hinv

theorem l17_t_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∉ ctxP t tau x₁ x₂ rho := by
  intro ht
  have hcent : t ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp ht).2
  have hYle : ctxYq t tau x₁ x₂ rho ≤ centralizer ({t} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcent y (ctxYq_le_ctxQ hy))
  have hYeq : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ :=
    (inf_eq_left.mpr hYle).symm.trans hc.Y_cent.1
  have hcardY := card_ctxYq hc.q_iso
  have hcardV := l17_card_V hc
  rw [hYeq] at hcardY
  omega

theorem l17_ttau_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t * tau ∉ ctxP t tau x₁ x₂ rho := by
  intro ht
  have hcent : t * tau ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp ht).2
  have hYle : ctxYq t tau x₁ x₂ rho ≤ centralizer ({t * tau} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcent y (ctxYq_le_ctxQ hy))
  have hYeq : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ :=
    (inf_eq_left.mpr hYle).symm.trans hc.Y_cent.2
  have hcardY := card_ctxYq hc.q_iso
  have hcardV := l17_card_V hc
  rw [hYeq] at hcardY
  omega

theorem l17_om_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    om ∉ ctxP t tau x₁ x₂ rho := by
  intro hom
  have hcent : om ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hom).2
  have hQle : ctxQ t tau x₁ x₂ rho ≤ centralizer ({om} : Set G) := by
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcent q hq)
  have hQeq : ctxQ t tau x₁ x₂ rho = ctxYq t tau x₁ x₂ rho :=
    (inf_eq_left.mpr hQle).symm.trans hc.Q_om.2.2.2.1
  have hcardQ := IsZ4Z4E4.card hc.q_iso
  have hcardY := card_ctxYq hc.q_iso
  rw [hQeq] at hcardQ
  omega

theorem l17_omtau_not_mem_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    om * tau ∉ ctxP t tau x₁ x₂ rho := by
  intro hom
  have hcent : om * tau ∈ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hom).2
  have hQle : ctxQ t tau x₁ x₂ rho ≤ centralizer ({om * tau} : Set G) := by
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcent q hq)
  have hQeq : ctxQ t tau x₁ x₂ rho = ctxYq t tau x₁ x₂ rho :=
    (inf_eq_left.mpr hQle).symm.trans hc.Q_omtau.2.2.2.1
  have hcardQ := IsZ4Z4E4.card hc.q_iso
  have hcardY := card_ctxYq hc.q_iso
  rw [hQeq] at hcardQ
  omega

theorem l17_D8_inf_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({t, om} : Set G) ⊓ ctxP t tau x₁ x₂ rho = ⊥ := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc
  have ht2' : t * t = 1 := by rwa [pow_two] at ht2
  have hom2' : om * om = 1 := by rwa [pow_two] at hom2
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_left hom2'
  have htom_sq : (t * om) ^ 2 = tau := by
    have hconj : om * t * om = t * tau := by simpa only [hom_inv] using hom_t
    rw [pow_two]
    calc (t * om) * (t * om) = t * (om * t * om) := by group
      _ = t * (t * tau) := by rw [hconj]
      _ = tau := by rw [← mul_assoc, ht2', one_mul]
  have hom_tau : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have hcomm : Commute (t * om) tau := by
    show (t * om) * tau = tau * (t * om)
    calc (t * om) * tau = t * (om * tau) := by rw [mul_assoc]
      _ = t * (tau * om) := by rw [hom_tau]
      _ = (t * tau) * om := by rw [mul_assoc]
      _ = (tau * t) * om := by rw [ht_tau]
      _ = tau * (t * om) := by rw [mul_assoc]
  have htomtau_sq : (t * om * tau) ^ 2 = tau := by
    have h := hcomm.mul_pow 2
    rw [htom_sq, htau2, mul_one] at h
    exact h
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxD, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxlist := (mem_closure_t_om_iff ht2 hom2 htau2 ht_tau hom_t x).mp hxD
  rcases hxlist with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact absurd hxP (l17_tau_not_mem_P hc)
  · exact absurd hxP (l17_t_not_mem_P hc)
  · exact absurd hxP (l17_ttau_not_mem_P hc)
  · exact absurd hxP (l17_om_not_mem_P hc)
  · exact absurd hxP (l17_omtau_not_mem_P hc)
  · have hmem : (t * om) ^ 2 ∈ ctxP t tau x₁ x₂ rho :=
      (ctxP t tau x₁ x₂ rho).pow_mem hxP 2
    rw [htom_sq] at hmem
    exact absurd hmem (l17_tau_not_mem_P hc)
  · have hmem : (t * om * tau) ^ 2 ∈ ctxP t tau x₁ x₂ rho :=
      (ctxP t tau x₁ x₂ rho).pow_mem hxP 2
    rw [htomtau_sq] at hmem
    exact absurd hmem (l17_tau_not_mem_P hc)

theorem l17_A_inf_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({tau, om} : Set G) ⊓ ctxP t tau x₁ x₂ rho = ⊥ := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc
  have htau2' : tau * tau = 1 := by rwa [pow_two] at htau2
  have hom2' : om * om = 1 := by rwa [pow_two] at hom2
  have hcomm : tau * om = om * tau := (om_tau_comm ht2 hom2 htau2 ht_tau hom_t).symm
  have hωtau : om * tau * om⁻¹ = tau * (1 : G) := by
    rw [mul_one, ← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxD, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxlist := (mem_closure_t_om_iff (t := tau) (τ := (1 : G)) (ω := om)
    htau2 hom2 (by simp) (by simp) hωtau x).mp hxD
  rcases hxlist with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact Subgroup.mem_bot.mpr rfl
  · exact absurd hxP (l17_tau_not_mem_P hc)
  · exact absurd (by simpa using hxP) (l17_tau_not_mem_P hc)
  · exact absurd hxP (l17_om_not_mem_P hc)
  · exact absurd (by simpa using hxP) (l17_om_not_mem_P hc)
  · rw [hcomm] at hxP
    exact absurd hxP (l17_omtau_not_mem_P hc)
  · rw [mul_one] at hxP
    rw [hcomm] at hxP
    exact absurd hxP (l17_omtau_not_mem_P hc)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
