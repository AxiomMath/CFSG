module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI1a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

lemma q13dI2b_t_om_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * om * t⁻¹ = om * tau := by
  have ht2 : t * t = 1 := q13a_t_mul_self h
  have hom2 : om * om = 1 := h.om_sq
  have hτcomm : tau * om = om * tau := (q13a_om_comm h).1.symm
  have homt : om * t = t * tau * om := by
    have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2
    have h1 : om * t * om = t * tau := by simpa [hom_inv] using h.t_om
    calc om * t = (om * t) * (om * om) := by rw [hom2, mul_one]
      _ = (om * t * om) * om := by group
      _ = (t * tau) * om := by rw [h1]
  calc t * om * t⁻¹ = t * (om * t) := by
        rw [inv_eq_of_mul_eq_one_right ht2]; group
    _ = t * (t * tau * om) := by rw [homt]
    _ = (t * t) * tau * om := by group
    _ = tau * om := by rw [ht2, one_mul]
    _ = om * tau := hτcomm

lemma q13dI2b_lam_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * tau * lam⁻¹ = tau := by
  rw [q13c_lam_cent_tau h]; group

lemma q13dI2b_lam_tauom (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hlo : lam * om * lam⁻¹ = om) : lam * (tau * om) * lam⁻¹ = tau * om := by
  calc lam * (tau * om) * lam⁻¹ = (lam * tau * lam⁻¹) * (lam * om * lam⁻¹) := by group
    _ = tau * om := by rw [q13dI2b_lam_tau h, hlo]

lemma q13dI2b_t_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * tau * t⁻¹ = tau := by
  rw [(q13a_t_comm h).2.2]; group

lemma q13dI2b_t_tauom (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * (tau * om) * t⁻¹ = om := by
  calc t * (tau * om) * t⁻¹ = (t * tau * t⁻¹) * (t * om * t⁻¹) := by group
    _ = tau * (om * tau) := by rw [q13dI2b_t_tau h, q13dI2b_t_om_conj h]
    _ = om := by
      calc tau * (om * tau) = (tau * om) * tau := by group
        _ = (om * tau) * tau := by rw [(q13a_om_comm h).1]
        _ = om * (tau * tau) := by group
        _ = om := by rw [q13a_tau_mul_self h, mul_one]

lemma q13dI2b_om_tau_om (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (om * tau) * om = tau := by
  calc (om * tau) * om = om * (tau * om) := by group
    _ = om * (om * tau) := by rw [(q13a_om_comm h).1]
    _ = (om * om) * tau := by group
    _ = tau := by rw [h.om_sq, one_mul]

lemma q13dI2b_inv_comm {x y : G} (h : x * y = y * x) : x⁻¹ * y = y * x⁻¹ := by
  have h1 : x⁻¹ * y * x = y := by
    calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x * y) := by rw [h]
      _ = y := by group
  calc x⁻¹ * y = (x⁻¹ * y * x) * x⁻¹ := by group
    _ = y * x⁻¹ := by rw [h1]

lemma q13dI2b_om_inv_comm (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} :
        Set G)) {b : G} (hbA : b ∈ q13A t tau x₁ x₂ rho) :
    om * b⁻¹ = b⁻¹ * om :=
  (q13dI2b_inv_comm (q13d_I_om_cent_A h hI b hbA).symm).symm

lemma q13dI2b_conj_gen (h : Q13Om t L S x₁ x₂ lam rho tau om)
    {a c : G} (ha : a ∈ q13A t tau x₁ x₂ rho) :
    (t * lam) * (a * c) * (t * lam)⁻¹ =
      (lam * a * lam⁻¹)⁻¹ * (t * (lam * c * lam⁻¹) * t⁻¹) := by
  have hlaA : lam * a * lam⁻¹ ∈ q13A t tau x₁ x₂ rho := (q13a_A_inv h a ha).2.1
  have h1 : t * (lam * a * lam⁻¹) * t⁻¹ = (lam * a * lam⁻¹)⁻¹ :=
    q13a_t_inv_A h _ hlaA
  calc (t * lam) * (a * c) * (t * lam)⁻¹
      = (t * (lam * a * lam⁻¹) * t⁻¹) * (t * (lam * c * lam⁻¹) * t⁻¹) := by group
    _ = (lam * a * lam⁻¹)⁻¹ * (t * (lam * c * lam⁻¹) * t⁻¹) := by rw [h1]

lemma q13dI2b_conj_cases (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hlo : lam * om * lam⁻¹ = om) {a : G} (ha : a ∈ q13A t tau x₁ x₂ rho) :
    (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ ∧
    (t * lam) * (a * tau) * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ * tau ∧
    (t * lam) * (a * om) * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ * (om * tau) ∧
    (t * lam) * (a * (tau * om)) * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ * om := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using q13dI2b_conj_gen h (c := 1) ha
  · have hgen := q13dI2b_conj_gen h (c := tau) ha
    rw [q13dI2b_lam_tau h, q13dI2b_t_tau h] at hgen
    exact hgen
  · have hgen := q13dI2b_conj_gen h (c := om) ha
    rw [hlo, q13dI2b_t_om_conj h] at hgen
    exact hgen
  · have hgen := q13dI2b_conj_gen h (c := tau * om) ha
    rw [q13dI2b_lam_tauom h hlo, q13dI2b_t_tauom h] at hgen
    exact hgen

lemma q13dI2b_mem_cent_of_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) {a : G}
    (hconj : (t * lam) * a * (t * lam)⁻¹ = a) :
    a ∈ centralizer ({t * lam} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h'' : (t * lam) * a = a * (t * lam) := by
    calc (t * lam) * a = ((t * lam) * a * (t * lam)⁻¹) * (t * lam) := by group
      _ = a * (t * lam) := by rw [hconj]
  exact h''.symm

lemma q13dI2b_tau_mem (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau ∈ closure ({t, om} : Set G) := by
  have hmem : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
      centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [h.c11.CO_center]
    exact Subgroup.mem_zpowers tau
  have h1 : tau ∈ ctxCO t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hmem).1
  rwa [h.CO_eq] at h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
