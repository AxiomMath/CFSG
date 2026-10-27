module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_tau_shift_A (h : Q13Om t L S x₁ x₂ lam rho tau om) {u X : G}
    (hu : u ∈ q13A t tau x₁ x₂ rho) (hX : X ∈ q13A t tau x₁ x₂ rho) :
    tau * u * (X * tau) = u * X := by
  have hcomm1 : tau * u = u * tau := (q13d_A_cent_tau h u hu).symm
  have hcomm2 : tau * X = X * tau := (q13d_A_cent_tau h X hX).symm
  calc tau * u * (X * tau) = (u * tau) * (X * tau) := by rw [hcomm1]
    _ = u * (tau * X) * tau := by group
    _ = u * (X * tau) * tau := by rw [hcomm2]
    _ = u * X * (tau * tau) := by group
    _ = u * X := by rw [q13a_tau_mul_self h, mul_one]

private theorem q13e_E3_stepA (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ w ∈ q13AN t tau x₁ x₂ rho,
      w⁻¹ * ((t * lam) * w * (t * lam)⁻¹) ∈ q13A t tau x₁ x₂ rho := by
  intro w hw
  obtain ⟨a, ha, hw1 | hw2⟩ := (q13e_mem_AN' h).mp hw
  · rw [hw1]
    rw [q13e_f_A h a ha]
    exact (q13A t tau x₁ x₂ rho).mul_mem ((q13A t tau x₁ x₂ rho).inv_mem ha)
      ((q13A t tau x₁ x₂ rho).inv_mem (q13a_A_inv h a ha).2.1)
  · rw [hw2]
    have hfa : (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ := q13e_f_A h a ha
    have hftau : (t * lam) * tau * (t * lam)⁻¹ = tau := q13e_f_tau h
    have hbA : (lam * a * lam⁻¹)⁻¹ ∈ q13A t tau x₁ x₂ rho :=
      (q13A t tau x₁ x₂ rho).inv_mem (q13a_A_inv h a ha).2.1
    have hexp : (t * lam) * (a * tau) * (t * lam)⁻¹ =
        ((t * lam) * a * (t * lam)⁻¹) * tau := by
      rw [show (t * lam) * (a * tau) * (t * lam)⁻¹ =
        ((t * lam) * a * (t * lam)⁻¹) * ((t * lam) * tau * (t * lam)⁻¹) by group, hftau]
    have hval : (a * tau)⁻¹ * ((t * lam) * (a * tau) * (t * lam)⁻¹)
        = a⁻¹ * (lam * a * lam⁻¹)⁻¹ := by
      calc (a * tau)⁻¹ * ((t * lam) * (a * tau) * (t * lam)⁻¹)
          = tau * a⁻¹ * ((lam * a * lam⁻¹)⁻¹ * tau) := by
            rw [hexp, hfa, show (a * tau)⁻¹ = tau⁻¹ * a⁻¹ by group,
              show tau⁻¹ = tau from inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
        _ = a⁻¹ * (lam * a * lam⁻¹)⁻¹ :=
            q13e_tau_shift_A h ((q13A t tau x₁ x₂ rho).inv_mem ha) hbA
    rw [hval]
    exact (q13A t tau x₁ x₂ rho).mul_mem ((q13A t tau x₁ x₂ rho).inv_mem ha) hbA

private theorem q13e_E3_stepB (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {k p : G}
    (hk : k ∈ q13CLP t tau x₁ x₂ rho om) (hp : p ∈ q13P t tau x₁ x₂ rho om)
    (hkp : (t * lam) * k * (t * lam)⁻¹ = k * p) :
    (t * lam) * ⁅t, k⁆ * (t * lam)⁻¹ = ⁅t, k⁆ * (p ^ 2)⁻¹ := by
  have hft : (t * lam) * t = t * (t * lam) := q13e_f_t h
  have hpCLP : p ∈ q13CLP t tau x₁ x₂ rho om := q13e_P_le_CLP h hD hp
  calc (t * lam) * ⁅t, k⁆ * (t * lam)⁻¹
      = ⁅t, (t * lam) * k * (t * lam)⁻¹⁆ := (q13e_kap_conj_t hft k).symm
    _ = ⁅t, k * p⁆ := by rw [hkp]
    _ = ⁅t, k⁆ * ⁅t, p⁆ := q13e_kap_mul_CLP h hD k hk p (Subgroup.mem_inf.mp hpCLP).1
    _ = ⁅t, k⁆ * (p ^ 2)⁻¹ := by rw [q13e_kap_P h hD p hp]

theorem q13e_E3 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13CLP t tau x₁ x₂ rho om,
      (t * lam) * k * (t * lam)⁻¹ * k⁻¹ ∈ q13P t tau x₁ x₂ rho om →
      ⁅t, k⁆ ∈ q13AN t tau x₁ x₂ rho → k ∈ q13P t tau x₁ x₂ rho om := by
  intro k hk hfix hw
  have hkL : k ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hk).1
  obtain ⟨p, hp, hkp⟩ := q13e_fix_rep h hD hkL hfix
  have hwA : (⁅t, k⁆)⁻¹ * ((t * lam) * ⁅t, k⁆ * (t * lam)⁻¹) ∈ q13A t tau x₁ x₂ rho :=
    q13e_E3_stepA h ⁅t, k⁆ hw
  have hstepB := q13e_E3_stepB h hD hk hp hkp
  have hp2invA : (p ^ 2)⁻¹ ∈ q13A t tau x₁ x₂ rho := by
    have heq : (⁅t, k⁆)⁻¹ * ((t * lam) * ⁅t, k⁆ * (t * lam)⁻¹) = (p ^ 2)⁻¹ := by
      rw [hstepB]; group
    rw [← heq]; exact hwA
  have hp2invN : (p ^ 2)⁻¹ ∈ ctxN tau x₁ x₂ :=
    (ctxN tau x₁ x₂).inv_mem (q13d_P_sq_mem_N h hD.A_cent p hp)
  have hp2invV : (p ^ 2)⁻¹ ∈ fourGrp x₁ x₂ := q13e_A_inf_N h (p ^ 2)⁻¹ hp2invA hp2invN
  have hp2V : p ^ 2 ∈ fourGrp x₁ x₂ := by
    simpa using (fourGrp x₁ x₂).inv_mem hp2invV
  have hpAN : p ∈ q13AN t tau x₁ x₂ rho := (q13e_mem_AN h hD).mpr ⟨hp, hp2V⟩
  have hpcoc : p * ((t * lam) * p * (t * lam)⁻¹) = 1 := q13e_cocycle h hkp
  have hpH1 : p ∈ q13H1 t tau x₁ x₂ lam rho := q13e_Z1_AN h p hpAN hpcoc
  have hkB : k ∈ q13B t tau x₁ x₂ rho om := q13e_CLP_le_B h hk
  have hkE0 : k ∈ q13E0 t tau x₁ x₂ rho om := q13e_class_one h hC hD hkB hpH1 hkp
  exact q13e_CLP_inf_E0 h hD k hk hkE0

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
