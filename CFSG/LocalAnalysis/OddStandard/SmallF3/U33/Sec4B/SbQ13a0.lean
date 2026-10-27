module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

structure Q13Om (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau om : G) : Prop extends
    Q13Ctx t L S x₁ x₂ lam rho tau where
  om_mem : om ∈ ctxCO t tau x₁ x₂ rho
  om_sq : om * om = 1
  om_not_mem : om ∉ closure {t, tau}
  t_om : om * t * om⁻¹ = t * tau
  CO_eq : ctxCO t tau x₁ x₂ rho = closure {t, om}


theorem q13a_exists_om (hq : Q13Ctx t L S x₁ x₂ lam rho tau) :
    ∃ om : G, Q13Om t L S x₁ x₂ lam rho tau om := by
  obtain ⟨om, hmem, hsq, hnot, hto⟩ := c13_exists_om hq.c11
  refine ⟨om, ?_⟩
  exact
    { toQ13Ctx := hq, om_mem := hmem, om_sq := hsq, om_not_mem := hnot, t_om := hto,
      CO_eq := c13_CO_eq hq.c11 hmem hsq hnot hto }

theorem q13a_t_mul_self (h : Q13Om t L S x₁ x₂ lam rho tau om) : t * t = 1 :=
  S4A.t_mul_self h.c11.hyp

theorem q13a_tau_mul_self (h : Q13Om t L S x₁ x₂ lam rho tau om) : tau * tau = 1 := by
  simpa [pow_two] using h.c11.l44.1

theorem q13a_lam_mul_self (h : Q13Om t L S x₁ x₂ lam rho tau om) : lam * lam = 1 := by
  have h1 := pow_orderOf_eq_one lam
  rw [h.c11.wreath.ord_lam] at h1
  simpa [pow_two] using h1

theorem q13a_rho_cube (h : Q13Om t L S x₁ x₂ lam rho tau om) : rho ^ 3 = 1 := by
  rw [← h.c11.ord_rho]
  exact pow_orderOf_eq_one rho

theorem q13a_t_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * lam = lam * t ∧ t * rho = rho * t ∧ t * tau = tau * t := by
  have hlamL : lam ∈ L := (S4A.generators_mem_L h.c11.toCtx0).2.2
  have hlamH : lam ∈ invCent t := S4A.L_le_invCent h.c11.hyp hlamL
  have hrhoH : rho ∈ invCent t := S4A.L_le_invCent h.c11.hyp h.c11.rho_mem
  have hX : CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) :=
    (Ctx4.ctxX_facts h.c11.toCtx10.toCtx4).1
  refine ⟨(S4A.mem_invCent_iff.mp hlamH).symm, (S4A.mem_invCent_iff.mp hrhoH).symm, ?_⟩
  exact CFSG.Open.IsElemAbelian.comm hX (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

theorem q13a_mem_M (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxM t tau x₁ x₂ ∧ tau ∈ ctxM t tau x₁ x₂ ∧ rho ∈ ctxM t tau x₁ x₂ ∧
      lam ∈ ctxM t tau x₁ x₂ ∧ om ∈ ctxM t tau x₁ x₂ := by
  have hgens := p0_gens_mem_M h.c11.toCtx4
  have hrl := l12_rho_lam_mem_M h.c11
  exact ⟨hgens.1, hgens.2.1, hrl.1, hrl.2,
    p0_O_le_M t tau x₁ x₂ (Subgroup.mem_inf.mp h.om_mem).1⟩

theorem q13a_conj_Q (h : Q13Om t L S x₁ x₂ lam rho tau om) {g a : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (ha : a ∈ ctxQ t tau x₁ x₂ rho) :
    g * a * g⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  h.c11.normal_Q.2 g hg a ha

theorem q13a_V_le_Q (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := by
  refine h.c11.phi_Q.1.trans ?_
  rw [ctxPhi]
  exact Subgroup.map_subtype_le _

theorem q13a_X_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ ctxX t tau x₁ x₂, ∀ b ∈ ctxX t tau x₁ x₂, a * b = b * a := by
  intro a ha b hb
  exact CFSG.Open.IsElemAbelian.comm (Ctx4.ctxX_facts h.c11.toCtx10.toCtx4).1 ha hb

theorem q13a_om_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * tau = tau * om ∧ om * rho = rho * om ∧ ∀ v ∈ fourGrp x₁ x₂, om * v = v * om := by
  have htau_cent : tau ∈ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    have hmem : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
        centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [h.c11.CO_center]
      exact Subgroup.mem_zpowers tau
    exact (Subgroup.mem_inf.mp hmem).2
  have hom_tau : om * tau = tau * om :=
    Subgroup.mem_centralizer_iff.mp htau_cent om h.om_mem
  have hom_rho : om * rho = rho * om :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h.om_mem).2
  have homO : om ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hmem : om ∈ ctxM t tau x₁ x₂ ⊓
        centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
      rw [← c13_O_cent h.c11]
      exact (Subgroup.mem_inf.mp h.om_mem).1
    exact (Subgroup.mem_inf.mp hmem).2
  exact ⟨hom_tau, hom_rho, fun v hv => (Subgroup.mem_centralizer_iff.mp homO v hv).symm⟩

theorem q13a_x₁_facts (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ ∈ ctxQ t tau x₁ x₂ rho ∧ x₁ ∈ baseGrp x₁ x₂ ∧ orderOf x₁ = 4 ∧
      tau * x₁ * tau⁻¹ = x₁⁻¹ ∧ x₁ ^ 2 ∈ fourGrp x₁ x₂ ∧ x₁ ^ 2 ≠ 1 := by
  have hx₁base : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  refine ⟨h.c11.base_le_Q hx₁base, hx₁base, h.c11.wreath.ord_x₁, h.c11.tau_x₁, ?_, ?_⟩
  · exact Subgroup.subset_closure (by simp)
  · intro h2
    have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [h.c11.wreath.ord_x₁] at hdvd
    omega

theorem q13a_om_not_mem_R (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om ∉ ctxR t tau x₁ x₂ := by
  intro homR
  apply h.om_not_mem
  have hmem : om ∈ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) :=
    ⟨homR, (Subgroup.mem_inf.mp h.om_mem).2⟩
  rwa [h.c11.CR_rho] at hmem

private lemma q13a_om_t (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om * t = t * tau * om := by
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right h.om_sq
  have h1 : om * t * om = t * tau := by simpa [hom_inv] using h.t_om
  have h2 : (om * t * om) * om = om * t := by rw [mul_assoc, h.om_sq, mul_one]
  rw [← h2, h1]

private def D8mem (t tau om x : G) : Prop :=
  x = 1 ∨ x = tau ∨ x = t ∨ x = t * tau ∨ x = om ∨ x = om * tau ∨ x = t * om ∨
    x = t * om * tau

private lemma q13a_D8_aux (h : Q13Om t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ closure {t, om}) :
    g = 1 ∨ g = tau ∨ g = t ∨ g = t * tau ∨ g = om ∨ g = om * tau ∨ g = t * om ∨
      g = t * om * tau := by
  have ht2 : t * t = 1 := q13a_t_mul_self h
  have hom2 : om * om = 1 := h.om_sq
  have hτ2 : tau * tau = 1 := q13a_tau_mul_self h
  have hτt : tau * t = t * tau := (q13a_t_comm h).2.2.symm
  have hτom : tau * om = om * tau := (q13a_om_comm h).1.symm
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2
  have hom_t : om * t = t * tau * om := q13a_om_t h
  have httτ : t * (t * tau) = tau := by rw [← mul_assoc, ht2, one_mul]
  have httω : t * (t * om) = om := by rw [← mul_assoc, ht2, one_mul]
  have httωτ : t * (t * om * tau) = om * tau := by
    calc t * (t * om * tau) = (t * t) * om * tau := by group
      _ = om * tau := by rw [ht2, one_mul]
  have homttau : om * (t * tau) = t * om := by
    calc om * (t * tau) = (om * t) * tau := by group
      _ = (t * tau * om) * tau := by rw [hom_t]
      _ = t * (tau * om) * tau := by group
      _ = t * (om * tau) * tau := by rw [hτom]
      _ = t * om * (tau * tau) := by group
      _ = t * om := by rw [hτ2, mul_one]
  have homomtau : om * (om * tau) = tau := by rw [← mul_assoc, hom2, one_mul]
  have homtom : om * (t * om) = t * tau := by
    calc om * (t * om) = (om * t) * om := by group
      _ = (t * tau * om) * om := by rw [hom_t]
      _ = t * tau := by rw [mul_assoc, hom2, mul_one]
  have hom_t' : om * t = t * om * tau := by
    rw [hom_t]
    calc t * tau * om = t * (tau * om) := by group
      _ = t * (om * tau) := by rw [hτom]
      _ = t * om * tau := by group
  have homtomtau : om * (t * om * tau) = t := by
    calc om * (t * om * tau) = (om * t) * om * tau := by group
      _ = (t * tau * om) * om * tau := by rw [hom_t]
      _ = ((t * tau) * (om * om)) * tau := by group
      _ = ((t * tau) * 1) * tau := by rw [hom2]
      _ = t * (tau * tau) := by group
      _ = t := by rw [hτ2, mul_one]
  have htQ : ∀ y, D8mem t tau om y → D8mem t tau om (t * y) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [D8mem]
    · simp [D8mem]
    · rw [ht2]; simp [D8mem]
    · rw [httτ]; simp [D8mem]
    · simp [D8mem]
    · rw [show t * (om * tau) = t * om * tau by group]; simp [D8mem]
    · rw [httω]; simp [D8mem]
    · rw [httωτ]; simp [D8mem]
  have homQ : ∀ y, D8mem t tau om y → D8mem t tau om (om * y) := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [D8mem]
    · simp [D8mem]
    · rw [hom_t']; simp [D8mem]
    · rw [homttau]; simp [D8mem]
    · rw [hom2]; simp [D8mem]
    · rw [homomtau]; simp [D8mem]
    · rw [homtom]; simp [D8mem]
    · rw [homtomtau]; simp [D8mem]
  change D8mem t tau om g
  refine Subgroup.closure_induction_left (s := ({t, om} : Set G))
    (p := fun x _ => D8mem t tau om x) (by simp [D8mem]) ?_ ?_ hg
  · intro x hx y hy ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htQ y ih
    · exact homQ y ih
  · intro x hx y hy ih
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [ht_inv]; exact htQ y ih
    · rw [hom_inv]; exact homQ y ih

private lemma q13a_tom_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * om) * (t * om) = tau := by
  have ht2 : t * t = 1 := q13a_t_mul_self h
  calc (t * om) * (t * om) = t * (om * t) * om := by group
    _ = t * (t * tau * om) * om := by rw [q13a_om_t h]
    _ = (t * t) * tau * (om * om) := by group
    _ = tau := by rw [ht2, h.om_sq]; group

private lemma q13a_tomtau_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (t * om * tau) * (t * om * tau) = tau := by
  have hcomm : tau * (t * om) = (t * om) * tau := by
    have htτ : t * tau = tau * t := (q13a_t_comm h).2.2
    have homτ : om * tau = tau * om := (q13a_om_comm h).1
    rw [← mul_assoc, htτ.symm, mul_assoc, homτ.symm, ← mul_assoc]
  have htom2 : (t * om) * (t * om) = tau := q13a_tom_sq h
  have hτ2 : tau * tau = 1 := q13a_tau_mul_self h
  calc (t * om * tau) * (t * om * tau)
      = (t * om) * (tau * (t * om)) * tau := by group
    _ = (t * om) * ((t * om) * tau) * tau := by rw [hcomm]
    _ = (t * om) * (t * om) * (tau * tau) := by group
    _ = tau * (tau * tau) := by rw [htom2]
    _ = tau := by rw [hτ2, mul_one]

theorem q13a_lam_om (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * om * lam⁻¹ = om ∨ lam * om * lam⁻¹ = om * tau := by
  set u : G := lam * om * lam⁻¹ with hu
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := (l12_rho_lam_mem_M h.c11).2
  have homO : om ∈ ctxO t tau x₁ x₂ := (Subgroup.mem_inf.mp h.om_mem).1
  have homrho : om * rho = rho * om :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h.om_mem).2
  have huO : u ∈ ctxO t tau x₁ x₂ :=
    (p0_normal_O t tau x₁ x₂).2 lam hlamM om homO
  have hcomm_urho : u * rho = rho * u := by
    have hlam_rho : lam * rho * lam⁻¹ = rho⁻¹ := h.c11.lam_rho
    have h1 : lam⁻¹ * rho * lam = rho⁻¹ := by
      have hρ : rho = lam⁻¹ * rho⁻¹ * lam := by
        calc rho = lam⁻¹ * (lam * rho * lam⁻¹) * lam := by group
          _ = lam⁻¹ * rho⁻¹ * lam := by rw [hlam_rho]
      calc lam⁻¹ * rho * lam = (lam⁻¹ * rho⁻¹ * lam)⁻¹ := by group
        _ = rho⁻¹ := by rw [← hρ]
    have h2 : om * rho⁻¹ * om⁻¹ = rho⁻¹ := by
      have h3 : om * rho * om⁻¹ = rho := by rw [homrho]; group
      calc om * rho⁻¹ * om⁻¹ = (om * rho * om⁻¹)⁻¹ := by group
        _ = rho⁻¹ := by rw [h3]
    have hconj : u * rho * u⁻¹ = rho := by
      calc u * rho * u⁻¹
          = lam * om * (lam⁻¹ * rho * lam) * om⁻¹ * lam⁻¹ := by
              rw [show u = lam * om * lam⁻¹ from hu]; group
        _ = lam * om * rho⁻¹ * om⁻¹ * lam⁻¹ := by rw [h1]
        _ = lam * (om * rho⁻¹ * om⁻¹) * lam⁻¹ := by group
        _ = lam * rho⁻¹ * lam⁻¹ := by rw [h2]
        _ = rho := by
              calc lam * rho⁻¹ * lam⁻¹ = (lam * rho * lam⁻¹)⁻¹ := by group
                _ = rho := by rw [hlam_rho, inv_inv]
    have h4 := congrArg (fun z => z * u) hconj
    simpa [mul_assoc] using h4
  have huCO : u ∈ ctxCO t tau x₁ x₂ rho := by
    rw [ctxCO]
    exact Subgroup.mem_inf.mpr
      ⟨huO, Subgroup.mem_centralizer_singleton_iff.mpr hcomm_urho⟩
  have hu_closure : u ∈ closure {t, om} := by
    rw [← h.CO_eq]
    exact huCO
  have hu2 : u * u = 1 := by
    calc u * u = lam * (om * om) * lam⁻¹ := by
          rw [show u = lam * om * lam⁻¹ from hu]; group
      _ = 1 := by rw [h.om_sq]; group
  have huR : u ∉ ctxR t tau x₁ x₂ := by
    intro huRmem
    apply q13a_om_not_mem_R h
    have hlinvM : lam⁻¹ ∈ ctxM t tau x₁ x₂ := (ctxM t tau x₁ x₂).inv_mem hlamM
    have hconjmem : lam⁻¹ * u * lam ∈ ctxR t tau x₁ x₂ := by
      simpa only [inv_inv] using h.c11.normal_R.2 lam⁻¹ hlinvM u huRmem
    have heq : lam⁻¹ * u * lam = om := by
      rw [show u = lam * om * lam⁻¹ from hu]; group
    rwa [heq] at hconjmem
  have htau_ne_one : tau ≠ 1 := fun h1 => h.c11.tau_not_mem (by rw [h1]; exact one_mem _)
  obtain hcases := q13a_D8_aux h hu_closure
  rcases hcases with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exfalso; apply huR; rw [h1]; exact one_mem _
  · exfalso; apply huR; rw [h1]
    exact h.c11.X_le_R (Subgroup.subset_closure (by simp))
  · exfalso; apply huR; rw [h1]
    exact h.c11.X_le_R (Subgroup.subset_closure (by simp))
  · exfalso; apply huR; rw [h1]
    exact h.c11.X_le_R (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  · left; exact h1
  · right; exact h1
  · exfalso
    have hsq : (t * om) * (t * om) = tau := q13a_tom_sq h
    rw [h1] at hu2
    exact htau_ne_one (by rw [← hsq]; exact hu2)
  · exfalso
    have hsq : (t * om * tau) * (t * om * tau) = tau := q13a_tomtau_sq h
    rw [h1] at hu2
    exact htau_ne_one (by rw [← hsq]; exact hu2)

theorem q13a_D8_cases (h : Q13Om t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ closure {t, om}) :
    g = 1 ∨ g = tau ∨ g = t ∨ g = t * tau ∨ g = om ∨ g = om * tau ∨ g = t * om ∨
      g = t * om * tau :=
  q13a_D8_aux h hg

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
