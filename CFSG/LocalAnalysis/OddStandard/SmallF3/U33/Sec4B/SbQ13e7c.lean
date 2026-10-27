module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e7a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e7b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e7c0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_phi_conj (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {r x : G}
    (hrL : r ∈ q13L t tau x₁ x₂ rho om) (hxL : x ∈ q13L t tau x₁ x₂ rho om)
    (hxr : x * r * x⁻¹ * r⁻¹ ∈ q13P t tau x₁ x₂ rho om) :
    ∀ q ∈ q13P t tau x₁ x₂ rho om,
      x * (r * q * r⁻¹ * q⁻¹) * x⁻¹ =
        r * (x * q * x⁻¹) * r⁻¹ * (x * q * x⁻¹)⁻¹ := by
  intro q hq
  set q' := x * q * x⁻¹ with hq'_def
  have hq'P : q' ∈ q13P t tau x₁ x₂ rho om := by
    rw [hq'_def]
    exact q13d_P_normal_L h hD.A_cent x hxL q hq
  set p := r⁻¹ * (x * r * x⁻¹ * r⁻¹) * r with hp_def
  have hpP : p ∈ q13P t tau x₁ x₂ rho om := by
    rw [hp_def]
    simpa using q13d_P_normal_L h hD.A_cent r⁻¹ (inv_mem hrL) (x * r * x⁻¹ * r⁻¹) hxr
  have hxr_eq : x * r * x⁻¹ = r * p := by
    rw [hp_def]
    group
  have hcomm : p * q' = q' * p := q13d_P_comm h hD.A_cent p hpP q' hq'P
  calc x * (r * q * r⁻¹ * q⁻¹) * x⁻¹
      = (x * r * x⁻¹) * q' * (x * r * x⁻¹)⁻¹ * q'⁻¹ := by
        rw [hq'_def]
        group
    _ = (r * p) * q' * (r * p)⁻¹ * q'⁻¹ := by rw [hxr_eq]
    _ = r * q' * r⁻¹ * q'⁻¹ := by
        rw [show (r * p) * q' * (r * p)⁻¹ * q'⁻¹ =
            r * (p * q') * p⁻¹ * r⁻¹ * q'⁻¹ by group, hcomm]
        group

private lemma q13e_phi_u (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {r x : G}
    (hrB : r ∈ q13B t tau x₁ x₂ rho om) (hxL : x ∈ q13L t tau x₁ x₂ rho om)
    (hrV : r * (t * om) * r⁻¹ * (t * om)⁻¹ ∈ fourGrp x₁ x₂)
    (hxr : x * r * x⁻¹ * r⁻¹ ∈ q13P t tau x₁ x₂ rho om)
    (hxV : ∀ v ∈ fourGrp x₁ x₂, x * v = v * x) :
    r * ((t * om)⁻¹ * (x * (t * om) * x⁻¹)) =
      ((t * om)⁻¹ * (x * (t * om) * x⁻¹)) * r := by
  have hrL : r ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hrB).1
  set γ := t * om with hγ_def
  set w := x * γ * x⁻¹ with hw_def
  set u := γ⁻¹ * w with hu_def
  have hγP : γ ∈ q13P t tau x₁ x₂ rho om := by
    rw [hγ_def]
    exact q13d_gam_mem_P h
  have hwP : w ∈ q13P t tau x₁ x₂ rho om := by
    rw [hw_def]
    exact q13d_P_normal_L h hD.A_cent x hxL γ hγP
  have huP : u ∈ q13P t tau x₁ x₂ rho om := by
    rw [hu_def]
    exact mul_mem (inv_mem hγP) hwP
  have hxu : x * γ * x⁻¹ = γ * u := by
    rw [hu_def, ← hw_def]
    group
  have hphiγ_V : r * γ * r⁻¹ * γ⁻¹ ∈ fourGrp x₁ x₂ := by
    rw [hγ_def]
    exact hrV
  have hφγ_cent : x * (r * γ * r⁻¹ * γ⁻¹) * x⁻¹ = r * γ * r⁻¹ * γ⁻¹ := by
    rw [hxV _ hphiγ_V]
    group
  have hconj := q13e_phi_conj h hD hrL hxL hxr γ hγP
  have hstep : r * (γ * u) * r⁻¹ * (γ * u)⁻¹ = r * γ * r⁻¹ * γ⁻¹ := by
    rw [← hxu, ← hconj]
    exact hφγ_cent
  have hmul := q13e_comm_BP_mul_right h hD r hrB γ hγP u huP
  have hthis : (r * γ * r⁻¹ * γ⁻¹) * 1 =
      (r * γ * r⁻¹ * γ⁻¹) * (r * u * r⁻¹ * u⁻¹) := by
    rw [mul_one]
    exact hstep.symm.trans hmul
  have hphi : r * u * r⁻¹ * u⁻¹ = 1 := (mul_left_cancel hthis).symm
  have hfin : (r * u) * (u * r)⁻¹ = 1 := by
    rw [mul_inv_rev]
    simpa [mul_assoc] using hphi
  exact mul_inv_eq_one.mp hfin

theorem q13e_R_cent_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ r ∈ q13R t tau x₁ x₂ rho om, ∀ a ∈ q13AN t tau x₁ x₂ rho, r * a = a * r := by
  intro r hr a ha
  obtain ⟨hrB, hrV⟩ := (q13e_mem_R).mp hr
  have hrrN : ∀ n ∈ ctxN tau x₁ x₂, n * r = r * n :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hrB).2
  obtain ⟨hx₁L, hx₂L⟩ := q13e_x_mem_L h hD
  obtain ⟨hx₁r, hx₂r⟩ := q13e_comm_x₁₂_B h hB hC hD r hrB
  have hx₁V : ∀ v ∈ fourGrp x₁ x₂, x₁ * v = v * x₁ := fun v hv => (q13e_x_cent_V h v hv).1
  have hx₂V : ∀ v ∈ fourGrp x₁ x₂, x₂ * v = v * x₂ := fun v hv => (q13e_x_cent_V h v hv).2
  set u₁ := (t * om)⁻¹ * (x₁ * (t * om) * x₁⁻¹) with hu₁_def
  set u₂ := (t * om)⁻¹ * (x₂ * (t * om) * x₂⁻¹) with hu₂_def
  have hu₁P : u₁ ∈ q13P t tau x₁ x₂ rho om := by
    rw [hu₁_def]
    exact q13e_u_mem_P h hD x₁ hx₁L
  have hu₂P : u₂ ∈ q13P t tau x₁ x₂ rho om := by
    rw [hu₂_def]
    exact q13e_u_mem_P h hD x₂ hx₂L
  have hu₁sq : u₁ ^ 2 = x₁ ^ 2 := by
    rw [hu₁_def]
    exact (q13e_u_sq h hD).1
  have hu₂sq : u₂ ^ 2 = x₂ ^ 2 := by
    rw [hu₂_def]
    exact (q13e_u_sq h hD).2
  have hcu₁ : r * u₁ = u₁ * r := by
    rw [hu₁_def]
    exact q13e_phi_u h hD hrB hx₁L hrV hx₁r hx₁V
  have hcu₂ : r * u₂ = u₂ * r := by
    rw [hu₂_def]
    exact q13e_phi_u h hD hrB hx₂L hrV hx₂r hx₂V
  have hcu₁₂ : r * (u₁ * u₂) = (u₁ * u₂) * r :=
    calc r * (u₁ * u₂) = (r * u₁) * u₂ := by group
      _ = (u₁ * r) * u₂ := by rw [hcu₁]
      _ = u₁ * (r * u₂) := by group
      _ = u₁ * (u₂ * r) := by rw [hcu₂]
      _ = (u₁ * u₂) * r := by group
  have hcover := q13e_AN_cover h hD hu₁P hu₂P hu₁sq hu₂sq a ha
  rcases hcover with hN | hN | hN | hN
  · exact (hrrN a hN).symm
  · have haeq : a = (a * u₁⁻¹) * u₁ := by group
    rw [haeq]
    calc r * ((a * u₁⁻¹) * u₁)
        = (r * (a * u₁⁻¹)) * u₁ := by group
      _ = ((a * u₁⁻¹) * r) * u₁ := by rw [(hrrN (a * u₁⁻¹) hN).symm]
      _ = (a * u₁⁻¹) * (r * u₁) := by group
      _ = (a * u₁⁻¹) * (u₁ * r) := by rw [hcu₁]
      _ = ((a * u₁⁻¹) * u₁) * r := by group
  · have haeq : a = (a * u₂⁻¹) * u₂ := by group
    rw [haeq]
    calc r * ((a * u₂⁻¹) * u₂)
        = (r * (a * u₂⁻¹)) * u₂ := by group
      _ = ((a * u₂⁻¹) * r) * u₂ := by rw [(hrrN (a * u₂⁻¹) hN).symm]
      _ = (a * u₂⁻¹) * (r * u₂) := by group
      _ = (a * u₂⁻¹) * (u₂ * r) := by rw [hcu₂]
      _ = ((a * u₂⁻¹) * u₂) * r := by group
  · have haeq : a = (a * (u₁ * u₂)⁻¹) * (u₁ * u₂) := by group
    rw [haeq]
    calc r * ((a * (u₁ * u₂)⁻¹) * (u₁ * u₂))
        = (r * (a * (u₁ * u₂)⁻¹)) * (u₁ * u₂) := by group
      _ = ((a * (u₁ * u₂)⁻¹) * r) * (u₁ * u₂) := by
            rw [(hrrN (a * (u₁ * u₂)⁻¹) hN).symm]
      _ = (a * (u₁ * u₂)⁻¹) * (r * (u₁ * u₂)) := by group
      _ = (a * (u₁ * u₂)⁻¹) * ((u₁ * u₂) * r) := by rw [hcu₁₂]
      _ = ((a * (u₁ * u₂)⁻¹) * (u₁ * u₂)) * r := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
