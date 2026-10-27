module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_comm_BP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ∀ p ∈ q13P t tau x₁ x₂ rho om,
      b * p * b⁻¹ * p⁻¹ ∈ ctxN tau x₁ x₂ := by
  intro b hb p hp
  obtain ⟨hbL, hbC⟩ := Subgroup.mem_inf.mp hb
  have hbpP : b * p * b⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent b hbL p hp
  have hp2N : p ^ 2 ∈ ctxN tau x₁ x₂ := q13d_P_sq_mem_N h hD.A_cent p hp
  have hbp2 : b * p ^ 2 * b⁻¹ = p ^ 2 := by
    have hc := Subgroup.mem_centralizer_iff.mp hbC (p ^ 2) hp2N
    rw [← hc]; group
  have hcsq : (b * p * b⁻¹) ^ 2 = p ^ 2 := by
    rw [conj_pow]
    exact hbp2
  have hcomm : Commute (b * p * b⁻¹) p⁻¹ :=
    q13d_P_comm h hD.A_cent (b * p * b⁻¹) hbpP p⁻¹ ((q13P t tau x₁ x₂ rho om).inv_mem hp)
  have hsq : (b * p * b⁻¹ * p⁻¹) ^ 2 = 1 := by
    calc (b * p * b⁻¹ * p⁻¹) ^ 2
        = (b * p * b⁻¹) ^ 2 * (p⁻¹) ^ 2 := hcomm.mul_pow 2
      _ = p ^ 2 * (p⁻¹) ^ 2 := by rw [hcsq]
      _ = 1 := by group
  exact q13d_P_sq_eq_one_mem_N h hD.A_cent (b * p * b⁻¹ * p⁻¹)
    ((q13P t tau x₁ x₂ rho om).mul_mem hbpP ((q13P t tau x₁ x₂ rho om).inv_mem hp)) hsq

theorem q13e_comm_BP_mul_right (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ∀ p ∈ q13P t tau x₁ x₂ rho om, ∀ q ∈ q13P t tau x₁ x₂ rho om,
      b * (p * q) * b⁻¹ * (p * q)⁻¹ = (b * p * b⁻¹ * p⁻¹) * (b * q * b⁻¹ * q⁻¹) := by
  intro b hb p hp q hq
  obtain ⟨hbL, _⟩ := Subgroup.mem_inf.mp hb
  have hbqP : b * q * b⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent b hbL q hq
  have hbpP : b * p * b⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent b hbL p hp
  have hpinv : p⁻¹ ∈ q13P t tau x₁ x₂ rho om := (q13P t tau x₁ x₂ rho om).inv_mem hp
  have hqinv : q⁻¹ ∈ q13P t tau x₁ x₂ rho om := (q13P t tau x₁ x₂ rho om).inv_mem hq
  have hBp : Commute (b * q * b⁻¹) p⁻¹ :=
    q13d_P_comm h hD.A_cent (b * q * b⁻¹) hbqP p⁻¹ hpinv
  have hpq : Commute p⁻¹ q⁻¹ := q13d_P_comm h hD.A_cent p⁻¹ hpinv q⁻¹ hqinv
  calc b * (p * q) * b⁻¹ * (p * q)⁻¹
      = ((b * p * b⁻¹) * (b * q * b⁻¹)) * (q⁻¹ * p⁻¹) := by group
    _ = ((b * p * b⁻¹) * (b * q * b⁻¹)) * (p⁻¹ * q⁻¹) := by rw [← hpq.eq]
    _ = (b * p * b⁻¹) * p⁻¹ * ((b * q * b⁻¹) * q⁻¹) :=
        Commute.mul_mul_mul_comm hBp (b * p * b⁻¹) q⁻¹
    _ = (b * p * b⁻¹ * p⁻¹) * (b * q * b⁻¹ * q⁻¹) := by group

theorem q13e_comm_BP_mul_left (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, ∀ b' ∈ q13B t tau x₁ x₂ rho om, ∀ p ∈ q13P t tau x₁ x₂ rho om,
      (b * b') * p * (b * b')⁻¹ * p⁻¹ = (b * p * b⁻¹ * p⁻¹) * (b' * p * b'⁻¹ * p⁻¹) := by
  intro b hb b' hb' p hp
  obtain ⟨hbL, hbC⟩ := Subgroup.mem_inf.mp hb
  have hn' : b' * p * b'⁻¹ * p⁻¹ ∈ ctxN tau x₁ x₂ := q13e_comm_BP h hD b' hb' p hp
  have hn : b * p * b⁻¹ * p⁻¹ ∈ ctxN tau x₁ x₂ := q13e_comm_BP h hD b hb p hp
  have hbn' : b * (b' * p * b'⁻¹ * p⁻¹) * b⁻¹ = b' * p * b'⁻¹ * p⁻¹ := by
    have hc := Subgroup.mem_centralizer_iff.mp hbC (b' * p * b'⁻¹ * p⁻¹) hn'
    rw [← hc]; group
  have hsplit : b' * p * b'⁻¹ = (b' * p * b'⁻¹ * p⁻¹) * p := by group
  calc (b * b') * p * (b * b')⁻¹ * p⁻¹
      = b * (b' * p * b'⁻¹) * b⁻¹ * p⁻¹ := by group
    _ = b * ((b' * p * b'⁻¹ * p⁻¹) * p) * b⁻¹ * p⁻¹ := by
        conv_lhs => rw [hsplit]
    _ = b * (b' * p * b'⁻¹ * p⁻¹) * p * b⁻¹ * p⁻¹ := by group
    _ = b * (b' * p * b'⁻¹ * p⁻¹) * b⁻¹ * (b * p * b⁻¹) * p⁻¹ := by group
    _ = (b' * p * b'⁻¹ * p⁻¹) * (b * p * b⁻¹) * p⁻¹ := by rw [hbn']
    _ = (b' * p * b'⁻¹ * p⁻¹) * (b * p * b⁻¹ * p⁻¹) := by group
    _ = (b * p * b⁻¹ * p⁻¹) * (b' * p * b'⁻¹ * p⁻¹) :=
        (q13d_P_comm h hD.A_cent _ (q13d_N_le_P h hn) _ (q13d_N_le_P h hn')).symm

theorem q13e_comm_tP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, t * p * t⁻¹ * p⁻¹ = (p ^ 2)⁻¹ := by
  intro p hp
  rw [hD.t_inv_P p hp]
  group

theorem q13e_sq_mem_CLP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, b * b ∈ q13CLP t tau x₁ x₂ rho om := by
  intro b hb
  obtain ⟨hbL, _⟩ := Subgroup.mem_inf.mp hb
  rw [q13CLP, Subgroup.mem_inf]
  refine ⟨(q13L t tau x₁ x₂ rho om).mul_mem hbL hbL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hmul := q13e_comm_BP_mul_left h hD b hb b hb p hp
  have hn : b * p * b⁻¹ * p⁻¹ ∈ ctxN tau x₁ x₂ := q13e_comm_BP h hD b hb p hp
  have hn2 : (b * p * b⁻¹ * p⁻¹) * (b * p * b⁻¹ * p⁻¹) = 1 := by
    simpa [pow_two] using (q13b_N_elemAbelian h).2 (b * p * b⁻¹ * p⁻¹) hn
  have h1 : (b * b) * p * (b * b)⁻¹ * p⁻¹ = 1 := by rw [hmul, hn2]
  have h2 : (b * b) * p * (b * b)⁻¹ = p := by
    rw [show (b * b) * p * (b * b)⁻¹ = ((b * b) * p * (b * b)⁻¹ * p⁻¹) * p by group,
      h1, one_mul]
  have h3 : (b * b) * p = p * (b * b) := by
    rw [show (b * b) * p = ((b * b) * p * (b * b)⁻¹) * (b * b) by group, h2]
  exact h3.symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
