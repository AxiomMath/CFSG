module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4q0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4q_V_comm_O (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g v : G}
    (hg : g ∈ ctxO t tau x₁ x₂) (hv : v ∈ fourGrp x₁ x₂) : g * v = v * g :=
  mul_inv_eq_iff_eq_mul.mp (w4q_V_central hc hg hv)

theorem w4q_sq_A_mem_V (hc : Ctx4C t L S x₁ x₂ lam rho tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : a * a ∈ fourGrp x₁ x₂ := by
  rw [hc.wreath.fourGrp_eq_mho]
  exact Subgroup.subset_closure ⟨a, ha, (pow_two a).symm⟩

theorem w4q_mem_V_of_sq_eq_one (hc : Ctx4C t L S x₁ x₂ lam rho tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) (h : a * a = 1) : a ∈ fourGrp x₁ x₂ := by
  rw [(hc.wreath.fourGrp_eq_omega).1]
  exact Subgroup.subset_closure ⟨ha, by rw [pow_two]; exact h⟩

theorem w4q_D_decomp
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {d : G}
    (hd : d ∈ ctxO t tau x₁ x₂) (hdt : d * t = t * d) :
    ∃ a ∈ baseGrp x₁ x₂, ∃ x ∈ ctxX t tau x₁ x₂, d = a * x := by
  have hE : ctxE t x₁ x₂ ≤ centralizer ({d} : Set G) := by
    rw [ctxE, Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hw with rfl | rfl | rfl
    · exact hdt.symm
    · exact (w4q_V_comm_O hc hd (Subgroup.subset_closure (by simp))).symm
    · exact (w4q_V_comm_O hc hd (Subgroup.subset_closure (by simp))).symm
  have hdC : d ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hE he)
  have hdclos : d ∈ closure ({t, tau, x₁, x₂} : Set G) := by
    rw [← hc.cent_E]
    exact ⟨hd, hdC⟩
  have hle : closure ({t, tau, x₁, x₂} : Set G) ≤ baseGrp x₁ x₂ ⊔ ctxX t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  obtain ⟨a, ha, x, hx, hax⟩ :=
    (mem_sup_iff_of_normalizes (fun k hk h hh => w4q_X_norm_A hc hk hh)).mp (hle hdclos)
  exact ⟨a, ha, x, hx, hax⟩

theorem w4q_tauea_sq
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {e a : G}
    (he : e ∈ ctxE t x₁ x₂) (ha : a ∈ baseGrp x₁ x₂) :
    (tau * e * a) * (tau * e * a) = 1 := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hτ2 := w4q_tau_mul_tau hc
  have hτinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hτ2
  have hτa : tau * a * tau = a⁻¹ := by
    have h := w4_tau_conj_baseGrp hc4 ha
    rwa [hτinv] at h
  have heX : e ∈ ctxX t tau x₁ x₂ := w4q_E_le_X t tau x₁ x₂ he
  have hτX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hea : e * a = a * e := w4q_A_cent_E hc ha he
  have heτ : e * tau = tau * e := w4_X_comm hc4 heX hτX
  have he2 : e * e = 1 := (w4q_X_facts hc).1.mul_self_eq_one heX
  calc (tau * e * a) * (tau * e * a) = tau * (e * a) * (tau * e * a) := by group
    _ = tau * (a * e) * (tau * e * a) := by rw [hea]
    _ = tau * a * (e * tau) * e * a := by group
    _ = tau * a * (tau * e) * e * a := by rw [heτ]
    _ = (tau * a * tau) * (e * e) * a := by group
    _ = a⁻¹ * 1 * a := by rw [hτa, he2]
    _ = 1 := by group

theorem w4q_sq_D
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {d : G}
    (hd : d ∈ ctxO t tau x₁ x₂) (hdt : d * t = t * d) : d * d ∈ fourGrp x₁ x₂ := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  obtain ⟨a, ha, x, hx, rfl⟩ := w4q_D_decomp hc hd hdt
  have hτ2 := w4q_tau_mul_tau hc
  have hτinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hτ2
  rcases w4q_X_cases hc hx with hxE | hτxE
  · have hxa : x * a = a * x := w4q_A_cent_E hc ha hxE
    have hx2 : x * x = 1 := (w4q_X_facts hc).1.mul_self_eq_one hx
    have h1 : (a * x) * (a * x) = a * a := by
      calc (a * x) * (a * x) = a * (x * a) * x := by group
        _ = a * (a * x) * x := by rw [hxa]
        _ = a * a * (x * x) := by group
        _ = a * a := by rw [hx2, mul_one]
    rw [h1]
    exact w4q_sq_A_mem_V hc ha
  · have hx' : x = tau * (tau * x) := by rw [← mul_assoc, hτ2, one_mul]
    have hτa' : tau * a⁻¹ * tau = a := by
      have h := w4_tau_conj_baseGrp hc4 (inv_mem ha)
      rwa [inv_inv, hτinv] at h
    have h1 : a * tau = tau * a⁻¹ := by
      calc a * tau = (tau * a⁻¹ * tau) * tau := by rw [hτa']
        _ = tau * a⁻¹ * (tau * tau) := by group
        _ = tau * a⁻¹ := by rw [hτ2, mul_one]
    have h2 : a⁻¹ * (tau * x) = (tau * x) * a⁻¹ :=
      (w4q_A_cent_E hc (inv_mem ha) hτxE).symm
    have h3 : a * x = tau * (tau * x) * a⁻¹ := by
      calc a * x = a * (tau * (tau * x)) := by rw [← hx']
        _ = (a * tau) * (tau * x) := by group
        _ = (tau * a⁻¹) * (tau * x) := by rw [h1]
        _ = tau * (a⁻¹ * (tau * x)) := by group
        _ = tau * ((tau * x) * a⁻¹) := by rw [h2]
        _ = tau * (tau * x) * a⁻¹ := by group
    rw [h3, w4q_tauea_sq hc hτxE (inv_mem ha)]
    exact one_mem _

theorem w4q_comm_O_A
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g a : G}
    (hg : g ∈ ctxO t tau x₁ x₂) (ha : a ∈ baseGrp x₁ x₂) :
    g * a * g⁻¹ * a⁻¹ ∈ ctxE t x₁ x₂ := by
  have hτ2 := w4q_tau_mul_tau hc
  have hcX : g * a * g⁻¹ * a⁻¹ ∈ ctxX t tau x₁ x₂ :=
    hc.O_quot.2 g hg a (w4q_A_le_O hc ha)
  rcases w4q_X_cases hc hcX with h | h
  · exact h
  · have hce : g * a * g⁻¹ * a⁻¹ = tau * (tau * (g * a * g⁻¹ * a⁻¹)) := by
      rw [← mul_assoc, hτ2, one_mul]
    have hga : g * a * g⁻¹ = tau * (tau * (g * a * g⁻¹ * a⁻¹)) * a := by
      calc g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
        _ = tau * (tau * (g * a * g⁻¹ * a⁻¹)) * a := by rw [← hce]
    have h1 : (g * a * g⁻¹) * (g * a * g⁻¹) = a * a := by
      have h2 : g * (a * a) * g⁻¹ = a * a := w4q_V_central hc hg (w4q_sq_A_mem_V hc ha)
      calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = a * a := h2
    have h3 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
      rw [hga]
      exact w4q_tauea_sq hc h ha
    have haa : a * a = 1 := by rw [← h1, h3]
    have haV : a ∈ fourGrp x₁ x₂ := w4q_mem_V_of_sq_eq_one hc ha haa
    rw [w4q_V_central hc hg haV, mul_inv_cancel]
    exact one_mem _

theorem w4q_comm_O_D
    (hc : Ctx4C t L S x₁ x₂ lam rho tau) {g d : G}
    (hg : g ∈ ctxO t tau x₁ x₂) (hd : d ∈ ctxO t tau x₁ x₂) (hdt : d * t = t * d) :
    g * d * g⁻¹ * d⁻¹ ∈ ctxE t x₁ x₂ := by
  obtain ⟨a, ha, x, hx, rfl⟩ := w4q_D_decomp hc hd hdt
  have hca := w4q_comm_O_A hc hg ha
  have hw : g * x * g⁻¹ * x⁻¹ ∈ fourGrp x₁ x₂ := w4q_O_comm_X hc hg hx
  have hVE := w4q_V_le_E t x₁ x₂
  have hVA := w4q_V_le_A x₁ x₂
  have hwa : a * (g * x * g⁻¹ * x⁻¹) * a⁻¹ = g * x * g⁻¹ * x⁻¹ := by
    rw [w4q_A_comm hc ha (hVA hw), mul_inv_cancel_right]
  have hid : g * (a * x) * g⁻¹ * (a * x)⁻¹ =
      (g * a * g⁻¹ * a⁻¹) * (a * (g * x * g⁻¹ * x⁻¹) * a⁻¹) := by group
  rw [hid, hwa]
  exact mul_mem hca (hVE hw)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
