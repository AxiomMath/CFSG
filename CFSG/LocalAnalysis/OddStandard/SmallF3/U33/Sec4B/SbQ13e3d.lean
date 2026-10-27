module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e3a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_commutator_mul_left_of_comm {a b x : G} (h : Commute b x) :
    ⁅a * b, x⁆ = ⁅a, x⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, h.commutator_eq]
  group

theorem q13e_kap_mul_CLP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13CLP t tau x₁ x₂ rho om, ∀ g ∈ q13L t tau x₁ x₂ rho om,
      ⁅t, k * g⁆ = ⁅t, k⁆ * ⁅t, g⁆ := by
  intro k hk g hg
  have hkcent : k ∈ centralizer ((q13P t tau x₁ x₂ rho om : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hk).2
  have hcP : ⁅t, g⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD g hg
  have hcomm : Commute k ⁅t, g⁆ :=
    (Subgroup.mem_centralizer_iff.mp hkcent ⁅t, g⁆ hcP).symm
  calc ⁅t, k * g⁆ = ⁅t, k⁆ * k * ⁅t, g⁆ * k⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj t k g
    _ = ⁅t, k⁆ * (k * ⁅t, g⁆ * k⁻¹) := by group
    _ = ⁅t, k⁆ * ⁅t, g⁆ := by rw [hcomm.mul_inv_cancel]

theorem q13e_kap_conj_CLP (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13L t tau x₁ x₂ rho om, ∀ k ∈ q13CLP t tau x₁ x₂ rho om,
      ⁅t, g * k * g⁻¹⁆ = g * ⁅t, k⁆ * g⁻¹ := by
  intro g hg k hk
  have hk'K : g * k * g⁻¹ ∈ q13CLP t tau x₁ x₂ rho om := q13e_CLP_normal_L h hD g hg k hk
  have hcx : Commute ⁅t, g⁆ (g * k * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk'K).2 ⁅t, g⁆ (q13e_kap_mem_P h hD g hg)
  have h1 : g * ⁅t, k⁆ * g⁻¹ = ⁅t * ⁅t, g⁆, g * k * g⁻¹⁆ := by
    rw [conjugate_commutatorElement (g₁ := t) (g₂ := k) (g₃ := g), q13e_conj_t h g]
  have h2 : ⁅t * ⁅t, g⁆, g * k * g⁻¹⁆ = ⁅t, g * k * g⁻¹⁆ :=
    q13e_commutator_mul_left_of_comm hcx
  exact h2.symm.trans h1.symm

theorem q13e_kap_ker_CLP (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13CLP t tau x₁ x₂ rho om, ⁅t, k⁆ = 1 → k ∈ ctxN tau x₁ x₂ := by
  intro k hk h1
  exact q13e_CK_t h hB hD k hk (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem q13e_CLP_sq_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ k ∈ q13CLP t tau x₁ x₂ rho om, k * k ∈ q13P t tau x₁ x₂ rho om := by
  intro k hk
  have hkK : k * k ∈ q13CLP t tau x₁ x₂ rho om := (q13CLP t tau x₁ x₂ rho om).mul_mem hk hk
  have hkL : k ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hk).1
  have hsq : ⁅t, k * k⁆ = ⁅t, k⁆ * ⁅t, k⁆ := q13e_kap_mul_CLP h hD k hk k hkL
  have hkapkP : ⁅t, k⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD k hkL
  have hcapNN : ⁅t, k * k⁆ ∈ ctxN tau x₁ x₂ := by
    rw [hsq, ← pow_two]
    exact q13d_P_sq_mem_N h hD.A_cent ⁅t, k⁆ hkapkP
  obtain ⟨p, hpP, hp_eq⟩ := q13e_kap_onto_N h hD (⁅t, k * k⁆)⁻¹ (inv_mem hcapNN)
  have hpK : p ∈ q13CLP t tau x₁ x₂ rho om := q13e_P_le_CLP h hD hpP
  have hpL : p ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hpK).1
  have hxK : k * k * p ∈ q13CLP t tau x₁ x₂ rho om :=
    (q13CLP t tau x₁ x₂ rho om).mul_mem hkK hpK
  have hx1 : ⁅t, k * k * p⁆ = 1 := by
    rw [q13e_kap_mul_CLP h hD (k * k) hkK p hpL, hp_eq]
    exact mul_inv_cancel _
  have hxN : k * k * p ∈ ctxN tau x₁ x₂ := q13e_kap_ker_CLP h hB hD (k * k * p) hxK hx1
  have hxP : k * k * p ∈ q13P t tau x₁ x₂ rho om := q13d_N_le_P h hxN
  have hsplit : k * k = (k * k * p) * p⁻¹ := by group
  rw [hsplit]
  exact (q13P t tau x₁ x₂ rho om).mul_mem hxP ((q13P t tau x₁ x₂ rho om).inv_mem hpP)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
