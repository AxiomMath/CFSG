module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18k
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

@[expose] def k18E0 (t tau x₁ x₂ lam rho om : G) : Subgroup G :=
  ctxQ t tau x₁ x₂ rho ⊔ closure {tau, om, lam * t}

theorem k18_E0_le_sylow (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    k18E0 t tau x₁ x₂ lam rho om ≤ 𝒮 := by
  refine sup_le (l18_le_sylow hc).1 ?_
  rw [Subgroup.closure_le]
  rintro x hx
  obtain ⟨htS, htauS, homS, hlamS⟩ := l18_T_le_sylow hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact htauS
  · exact homS
  · exact Subgroup.mul_mem _ hlamS htS

theorem k18_E0_cent_W (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    k18E0 t tau x₁ x₂ lam rho om ≤
      centralizer ((ctxYq t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) : Subgroup G) :
        Set G) := by
  refine sup_le ?_ ?_
  · intro q hq
    exact Subgroup.mem_centralizer_iff.mpr
      (fun w hw => IsZ4Z4E4.comm hc.q_iso (ctxYq_le_ctxQ hw.1) hq)
  · rw [Subgroup.closure_le]
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · intro w hw
      exact (hc.tau_cent_Y w hw.1).symm
    · intro w hw
      exact (hc.om_cent_Y w hw.1).symm
    · intro w hw
      exact ((Subgroup.mem_centralizer_iff.mp hw.2) (lam * t) (by simp)).symm

theorem k18_t_om (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : t * om * t⁻¹ = om * tau := by
  obtain ⟨ht2, -, hom2, -, -, ht_tau, hom_t⟩ := ctx13_relations hc
  have ht2' : t * t = 1 := by rw [pow_two] at ht2; exact ht2
  have hom2' : om * om = 1 := by rw [pow_two] at hom2; exact hom2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
  have homi : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2'
  have h1 : om * (om * t * om) = t * om := by
    calc om * (om * t * om) = (om * om) * (t * om) := by group
      _ = t * om := by rw [hom2', one_mul]
  have hom_t' : om * t * om = t * tau := by
    rw [homi] at hom_t
    exact hom_t
  have key : t * om = om * (t * tau) := by
    rw [← h1, hom_t']
  have htτt : (t * tau) * t = tau := by rw [ht_tau, mul_assoc, ht2', mul_one]
  calc t * om * t⁻¹ = t * om * t := by rw [hti]
    _ = om * (t * tau) * t := by rw [key]
    _ = om * ((t * tau) * t) := by rw [mul_assoc]
    _ = om * tau := by rw [htτt]

theorem k18_B0_le_derived (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G}
    {v₁ v₂ : G} (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    k18B0 t tau x₁ x₂ rho ≤
      ⁅k18E0 t tau x₁ x₂ lam rho om, k18E0 t tau x₁ x₂ lam rho om⁆ := by
  set E : Subgroup G := k18E0 t tau x₁ x₂ lam rho om with hE
  obtain ⟨hV1, -, hVQ, -, -, -, hVY, -, hv₁V, -, -, hv₂V, -, hVgen, -, hv₂u, -, hω₁, -⟩ := hV
  have hQ : ctxQ t tau x₁ x₂ rho ≤ E := by rw [hE]; exact le_sup_left
  have hclos : closure ({tau, om, lam * t} : Set G) ≤ E := by rw [hE]; exact le_sup_right
  have htauE : tau ∈ E := hclos (Subgroup.subset_closure (by simp))
  have homE : om ∈ E := hclos (Subgroup.subset_closure (by simp))
  have huE : lam * t ∈ E := hclos (Subgroup.subset_closure (by simp))
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₁E : x₁ ∈ E := hQ hx₁Q
  have hxxQ : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho := mul_mem hx₁Q hx₂Q
  have hxxE : x₁ * x₂ ∈ E := hQ hxxQ
  have hV'Q : V' ≤ ctxQ t tau x₁ x₂ rho := by rw [hVQ]; exact le_sup_right
  have hv₂Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := hV'Q hv₂V
  have hv₂E : v₂ ∈ E := hQ hv₂Q
  have hfourQ : fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := by
    rw [fourGrp, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact pow_mem hx₁Q 2
    · exact pow_mem hxxQ 2
  have hmem : ∀ {a b : G}, a ∈ E → b ∈ E → ⁅a, b⁆ ∈ ⁅E, E⁆ :=
    fun ha hb => Subgroup.commutator_mem_commutator ha hb
  have homCO : om ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_eq]; exact Subgroup.subset_closure (by simp)
  have htau_cent_CO : tau ∈ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    have h : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
        centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [hc.CO_center]; exact Subgroup.mem_zpowers tau
    exact h.2
  have hom_tau_comm : om * tau = tau * om :=
    Subgroup.mem_centralizer_iff.mp htau_cent_CO om homCO
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc).1
    rw [pow_two] at h; exact h
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hom2' : om * om = 1 := by
    have h := hc.om_sq
    rw [pow_two] at h; exact h
  have homi : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2'
  have hlam2' : lam * lam = 1 := by
    have h := (ctx13_lam_facts hc).1
    rw [pow_two] at h; exact h
  have hlami : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right hlam2'
  have hlam_om : lam * om = om * lam := (l17_lam_comm hc).2.2
  have hlam_tau : lam * tau = tau * lam := (l17_lam_comm hc).2.1
  have hom_t : t * om * t = om * tau := by
    have h := k18_t_om hc
    rwa [hti] at h
  have hx₁4 : x₁ ^ 4 = 1 := by rw [← hc.wreath.ord_x₁]; exact pow_orderOf_eq_one x₁
  have hx₁sq_mul : x₁ ^ 2 * x₁ ^ 2 = 1 := by
    rw [← pow_add, show (2 : ℕ) + 2 = 4 from rfl, hx₁4]
  have hx₁sq_inv : (x₁ ^ 2)⁻¹ = x₁ ^ 2 := inv_eq_of_mul_eq_one_right hx₁sq_mul
  have hy_eq : ⁅tau, x₁⁆ = x₁ ^ 2 := by
    rw [commutatorElement_def, hc.tau_x₁]
    rw [show x₁⁻¹ * x₁⁻¹ = (x₁ ^ 2)⁻¹ by rw [pow_two, mul_inv_rev]]
    exact hx₁sq_inv
  have hyD : x₁ ^ 2 ∈ ⁅E, E⁆ := hy_eq ▸ hmem htauE hx₁E
  have hzsq_inv : ((x₁ * x₂) ^ 2)⁻¹ = (x₁ * x₂) ^ 2 :=
    inv_eq_of_mul_eq_one_right hc.wreath.sq_x₁x₂_mul_self
  have htau_x₁x₂ : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
    rw [show tau * (x₁ * x₂) * tau⁻¹ =
        (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) by group, hc.tau_x₁, hc.tau_x₂,
      mul_inv_rev]
    rw [← mul_inv_rev, ← mul_inv_rev, hc.wreath.comm]
  have hz_eq : ⁅tau, x₁ * x₂⁆ = (x₁ * x₂) ^ 2 := by
    rw [commutatorElement_def, htau_x₁x₂, ← mul_inv_rev, ← pow_two]
    exact hzsq_inv
  have hzD : (x₁ * x₂) ^ 2 ∈ ⁅E, E⁆ := hz_eq ▸ hmem htauE hxxE
  have hfourD : fourGrp x₁ x₂ ≤ ⁅E, E⁆ := by
    rw [fourGrp, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hyD
    · exact hzD
  have hV'comm : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
    haveI : IsMulCommutative ↥V' := hV1.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : V') ⟨b, hb⟩)
  have hv₁v₂ : v₁ * v₂ = v₂ * v₁ := hV'comm v₁ hv₁V v₂ hv₂V
  have hv₂v₁ : v₂ * v₁ * v₂⁻¹ = v₁ := by
    rw [← hv₁v₂, mul_assoc, mul_inv_cancel, mul_one]
  have hv₁_eq : ⁅lam * t, v₂⁆ = v₁ := by
    rw [commutatorElement_def, hv₂u]
    exact hv₂v₁
  have hv₁D : v₁ ∈ ⁅E, E⁆ := hv₁_eq ▸ hmem huE hv₂E
  obtain ⟨w, hwfour, hw_eq⟩ := hω₁
  have hwQ : w ∈ ctxQ t tau x₁ x₂ rho := hfourQ hwfour
  have hx₁_v₂w : x₁ * (v₂ * w) = (v₂ * w) * x₁ := by
    calc x₁ * (v₂ * w) = (x₁ * v₂) * w := by rw [mul_assoc]
      _ = (v₂ * x₁) * w := by rw [IsZ4Z4E4.comm hc.q_iso hx₁Q hv₂Q]
      _ = v₂ * (x₁ * w) := by rw [mul_assoc]
      _ = v₂ * (w * x₁) := by rw [IsZ4Z4E4.comm hc.q_iso hx₁Q hwQ]
      _ = (v₂ * w) * x₁ := by rw [mul_assoc]
  have hvw_eq : v₂ * w = ⁅om, x₁⁆ := by
    rw [commutatorElement_def, hw_eq]
    rw [mul_assoc x₁ v₂ w, hx₁_v₂w, mul_assoc, mul_inv_cancel, mul_one]
  have hwD : w ∈ ⁅E, E⁆ := hfourD hwfour
  have hv₂wD : v₂ * w ∈ ⁅E, E⁆ := hvw_eq ▸ hmem homE hx₁E
  have hv₂D : v₂ ∈ ⁅E, E⁆ := by
    have h : (v₂ * w) * w⁻¹ ∈ ⁅E, E⁆ := Subgroup.mul_mem _ hv₂wD (Subgroup.inv_mem _ hwD)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h
  have hxx_eq : ⁅lam * t, x₁⁆ * x₁ ^ 2 = x₁ * x₂ := by
    rw [commutatorElement_def, k18_u_x₁ hc]
    rw [show x₂ * x₁⁻¹ * x₁ ^ 2 = x₂ * x₁ by group]
    exact hc.wreath.comm.symm
  have hux₁D : ⁅lam * t, x₁⁆ ∈ ⁅E, E⁆ := hmem huE hx₁E
  have hxxD : x₁ * x₂ ∈ ⁅E, E⁆ := hxx_eq ▸ Subgroup.mul_mem _ hux₁D hyD
  have hu_inv : (lam * t)⁻¹ = t * lam := by rw [mul_inv_rev, hti, hlami]
  have hfinal : lam * (om * tau) * lam = om * tau := by
    calc lam * (om * tau) * lam = (lam * om) * (tau * lam) := by group
      _ = (om * lam) * (tau * lam) := by rw [hlam_om]
      _ = om * (lam * tau) * lam := by group
      _ = om * (tau * lam) * lam := by rw [hlam_tau]
      _ = om * tau * (lam * lam) := by group
      _ = om * tau := by rw [hlam2', mul_one]
  have hu_om : (lam * t) * om * (lam * t)⁻¹ = om * tau := by
    rw [hu_inv]
    calc (lam * t) * om * (t * lam) = lam * (t * om * t) * lam := by group
      _ = lam * (om * tau) * lam := by rw [hom_t]
      _ = om * tau := hfinal
  have htau_eq : ⁅lam * t, om⁆ = tau := by
    rw [commutatorElement_def, hu_om, homi, hom_tau_comm, mul_assoc, hom2',
      mul_one]
  have htauD : tau ∈ ⁅E, E⁆ := htau_eq ▸ hmem huE homE
  have hV'D : V' ≤ ⁅E, E⁆ := by
    rw [hVgen, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hv₁D
    · exact hv₂D
  have hYD : ctxYq t tau x₁ x₂ rho ≤ ⁅E, E⁆ := by
    rw [hVY]
    exact sup_le hfourD hV'D
  have hclosD : closure ({x₁ * x₂, tau} : Set G) ≤ ⁅E, E⁆ := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hxxD
    · exact htauD
  rw [k18B0]
  exact sup_le hYD hclosD

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
