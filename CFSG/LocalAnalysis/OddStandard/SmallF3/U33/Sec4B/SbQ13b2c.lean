module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_comm_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) {q d g : G}
    (hq : q ∈ ctxQ t tau x₁ x₂ rho) (hd : d ∈ ctxCO t tau x₁ x₂ rho)
    (hg : g ∈ ctxCO t tau x₁ x₂ rho)
    (hcomm : g * (q * d) * g⁻¹ * (q * d)⁻¹ ∈ ctxQ t tau x₁ x₂ rho) : g * d = d * g := by
  set c : G := g * (q * d) * g⁻¹ * (q * d)⁻¹ with hc
  set w : G := g * d * g⁻¹ * d⁻¹ with hw
  have hgO : g ∈ ctxO t tau x₁ x₂ := (Subgroup.mem_inf.mp hg).1
  have hgM : g ∈ ctxM t tau x₁ x₂ := p0_O_le_M t tau x₁ x₂ hgO
  have hgq : g * q * g⁻¹ ∈ ctxQ t tau x₁ x₂ rho := q13a_conj_Q h hgM hq
  have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := hcomm
  have hwQ : w ∈ ctxQ t tau x₁ x₂ rho := by
    have heq : w = (g * q * g⁻¹)⁻¹ * c * q := by rw [hw, hc]; group
    rw [heq]
    exact (ctxQ t tau x₁ x₂ rho).mul_mem
      ((ctxQ t tau x₁ x₂ rho).mul_mem ((ctxQ t tau x₁ x₂ rho).inv_mem hgq) hcQ) hq
  have hwCO : w ∈ ctxCO t tau x₁ x₂ rho := by
    have hdO : d ∈ ctxO t tau x₁ x₂ := (Subgroup.mem_inf.mp hd).1
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (ctxO t tau x₁ x₂).mul_mem ((ctxO t tau x₁ x₂).mul_mem
        ((ctxO t tau x₁ x₂).mul_mem hgO hdO) ((ctxO t tau x₁ x₂).inv_mem hgO))
        ((ctxO t tau x₁ x₂).inv_mem hdO)
    · exact (centralizer ({rho} : Set G)).mul_mem ((centralizer ({rho} : Set G)).mul_mem
        ((centralizer ({rho} : Set G)).mul_mem (Subgroup.mem_inf.mp hg).2
          (Subgroup.mem_inf.mp hd).2)
        ((centralizer ({rho} : Set G)).inv_mem (Subgroup.mem_inf.mp hg).2))
        ((centralizer ({rho} : Set G)).inv_mem (Subgroup.mem_inf.mp hd).2)
  have hw1 : w = 1 := q13b_Q_inf_CO h w hwQ hwCO
  have h2 : g * d * g⁻¹ * d⁻¹ = 1 := by rw [← hw]; exact hw1
  have h3 : g * d * g⁻¹ = d := mul_inv_eq_one.mp h2
  calc g * d = (g * d * g⁻¹) * g := by group
    _ = d * g := by rw [h3]

theorem q13b_core (h : Q13Om t L S x₁ x₂ lam rho tau om) {f : G}
    (hfO : f ∈ ctxO t tau x₁ x₂) (hf2 : f * f = 1)
    (ha : t * f * t⁻¹ * f⁻¹ ∈ fourGrp x₁ x₂) (hb : om * f * om⁻¹ * f⁻¹ ∈ fourGrp x₁ x₂) :
    f ∈ ctxN tau x₁ x₂ := by
  have hV := (h.c11.wreath.fourGrp_eq_omega).2.1
  have htau_comm : tau * f = f * tau :=
    q13b_tau_comm_aux (q13a_t_mul_self h) h.om_sq h.t_om
      (fun a ha b hb => CFSG.Open.IsElemAbelian.comm hV ha hb)
      (fun a ha => CFSG.Open.IsElemAbelian.mul_self_eq_one hV ha)
      (fun a ha => q13b_O_cent_V h t (q13b_t_mem_O h) a ha)
      (fun a ha => q13b_O_cent_V h om (q13b_om_mem_O h) a ha) ha hb
  have hnorm : ∀ k ∈ ctxCO t tau x₁ x₂ rho, ∀ a ∈ ctxQ t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    intro k hk a ha
    exact q13a_conj_Q h (p0_O_le_M t tau x₁ x₂ (Subgroup.mem_inf.mp hk).1) ha
  have hfO' : f ∈ ctxQ t tau x₁ x₂ rho ⊔ ctxCO t tau x₁ x₂ rho := by
    simpa only [q13b_O_eq h] using hfO
  obtain ⟨q, hqQ, d, hdCO, hfqd⟩ := (mem_sup_iff_of_normalizes hnorm).mp hfO'
  have htCO : t ∈ ctxCO t tau x₁ x₂ rho := by
    rw [h.CO_eq]; exact Subgroup.subset_closure (by simp)
  have htd : t * d = d * t := by
    apply q13b_comm_CO h hqQ hdCO htCO
    simpa only [← hfqd] using q13a_V_le_Q h ha
  have homd : om * d = d * om := by
    apply q13b_comm_CO h hqQ hdCO h.om_mem
    simpa only [← hfqd] using q13a_V_le_Q h hb
  have hle : closure ({t, om} : Set G) ≤ centralizer ({d} : Set G) := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr htd
    · exact Subgroup.mem_centralizer_singleton_iff.mpr homd
  have hd_cent : d ∈ centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [h.CO_eq]
    refine Subgroup.mem_centralizer_iff.mpr (fun z hz => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  have hd_inf : d ∈ ctxCO t tau x₁ x₂ rho ⊓
      centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := ⟨hdCO, hd_cent⟩
  have hd_tau : d ∈ zpowers tau := by
    rwa [h.c11.CO_center] at hd_inf
  have hd_cases : d = 1 ∨ d = tau := q13b_mem_zpowers_sq (q13a_tau_mul_self h) hd_tau
  have hd2 : d * d = 1 := by
    rcases hd_cases with h1 | h1
    · rw [h1]; group
    · rw [h1]; exact q13a_tau_mul_self h
  have hdN : d ∈ ctxN tau x₁ x₂ := by
    rcases hd_cases with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact q13b_tau_mem_N h
  have hdf : d * f = f * d := by
    rcases hd_cases with h1 | h1
    · rw [h1]; group
    · rw [h1]; exact htau_comm
  have hd_comm_tau : tau * d = d * tau := by
    rcases hd_cases with h1 | h1
    · rw [h1]; group
    · rw [h1]
  have hqf : q = f * d := by
    rw [hfqd, mul_assoc, hd2, mul_one]
  have hq2 : q * q = 1 := by
    rw [hqf]
    calc (f * d) * (f * d) = f * (d * f) * d := by group
      _ = f * (f * d) * d := by rw [hdf]
      _ = (f * f) * (d * d) := by group
      _ = 1 := by rw [hf2, hd2, one_mul]
  have hq_comm : q * tau = tau * q := by
    rw [hqf]
    calc (f * d) * tau = f * (d * tau) := by group
      _ = f * (tau * d) := by rw [← hd_comm_tau]
      _ = (f * tau) * d := by group
      _ = (tau * f) * d := by rw [← htau_comm]
      _ = tau * (f * d) := by group
  have hqA : q ∈ q13A t tau x₁ x₂ rho := by
    rw [q13A]
    exact Subgroup.mem_inf.mpr ⟨hqQ, Subgroup.mem_centralizer_singleton_iff.mpr hq_comm⟩
  have hqV : q ∈ fourGrp x₁ x₂ := q13b_omega1_A h q hqA hq2
  rw [hfqd]
  exact (ctxN tau x₁ x₂).mul_mem (q13b_V_le_N h hqV) hdN

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
